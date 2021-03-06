#include <MeOrion.h>
#include <EEPROM.h>
#include <SoftwareSerial.h>
#include <Wire.h>


union {
    struct{
      char name[8];
      unsigned char motoADir;
      unsigned char motoBDir;
      int arm0len;
      int arm1len;
      int speed;
      int penUpPos;
      int penDownPos; 
      int spongePos; 
    } data;
    char buf[64];
} roboSetup;

// arduino only handle A,B step mapping
float curSpd, tarSpd; // speed profile
float curX, curY, curZ;
float tarX, tarY, tarZ; // target xyz position
float curTh1, curTh2;
float tarTh1, tarTh2; // target angle of joint
int tarA, tarB, posA, posB; // target stepper position
int8_t motorAfw, motorAbk;
int8_t motorBfw, motorBbk;
long last_time;
MePort stpB(PORT_2);
MePort stpA(PORT_1);
MeDCMotor laser(M2);
MePort servoPort(PORT_7);
int servopin = servoPort.pin2();
Servo servoPen;

int colorPoint[18][2] = {
  {-15, -332}, {-55, -332}, {-90, -332}, {-125, -332}, {-160, -332}, {-200, -332},
  {-15, -297}, {-55, -297}, {-90, -297}, {-125, -297}, {-160, -297}, {-200, -297},
  {-15, -262}, {-55, -262}, {-90, -262}, {-125, -262}, {-160, -262}, {-200, -262}
};

int waterPoint[2] = {-272, -315};
int spongePoint[3][2] = {{-352, -276}, {-373, -256}, {-385, -239}};

int prevColorPos = -1;
bool spotDraw = false;

// Arm Length
#define ARML1 248
#define ARML2 206
/************** motor movements ******************/
void stepperMoveA(int dir) {
//  Serial.printf("stepper A %d\n",dir);
  if (dir > 0) {
    stpA.dWrite1(LOW);
  } else {
    stpA.dWrite1(HIGH);
  }
  stpA.dWrite2(HIGH);
  stpA.dWrite2(LOW);
}


void stepperMoveB(int dir) {
//  Serial.printf("stepper B %d\n",dir);
  if (dir > 0) {
    stpB.dWrite1(LOW);
  } else {
    stpB.dWrite1(HIGH);
  }
  stpB.dWrite2(HIGH);
  stpB.dWrite2(LOW);
}

/************** scara inversekinect **********************/
// th1 solution
//2*atan((2*L1*y + (- L1^4 + 2*L1^2*L2^2 + 2*L1^2*x^2 + 2*L1^2*y^2 - L2^4 + 2*L2^2*x^2 + 2*L2^2*y^2 - x^4 - 2*x^2*y^2 - y^4)^(1/2))/(L1^2 - 2*L1*x - L2^2 + x^2 + y^2))
// th2 solution
//2*atan(((- L1^2 + 2*L1*L2 - L2^2 + x^2 + y^2)*(L1^2 + 2*L1*L2 + L2^2 - x^2 - y^2))^(1/2)/(L1^2 + 2*L1*L2 + L2^2 - x^2 - y^2))
float th1, th2;
void scaraInverseKinect(float x, float y) {
  // convert x, y position to servo angle
  float L1 = roboSetup.data.arm0len;
  float L2 = roboSetup.data.arm1len;
  //Serial.print("x ");Serial.println(x);
  //Serial.print("y ");Serial.println(y);
  th1 = 2 * atan((2 * L1 * y + sqrt(- L1 * L1 * L1 * L1 + 2 * L1 * L1 * L2 * L2 + 2*L1*L1*x*x + 2*L1*L1*y*y - L2*L2*L2*L2 + 2*L2*L2*x*x + 2*L2*L2*y*y - x*x*x*x - 2*x*x*y*y - y*y*y*y))/(L1*L1 - 2*L1*x - L2*L2 + x*x + y*y));
  th2 = 2 * atan(sqrt((- L1 * L1 + 2 * L1 * L2 - L2 * L2 + x * x + y * y) * (L1*L1 + 2*L1*L2 + L2*L2 - x*x - y*y))/(L1*L1 + 2*L1*L2 + L2*L2 - x*x - y*y));
  //Serial.print("th1 ");Serial.println(th1/PI*180);
  //Serial.print("th2 ");Serial.println(th2/PI*180);
}

#define STEPS_PER_CIRCLE 16000.0f
long pos1, pos2;
void thetaToSteps(float th1, float th2) {
  pos1 = round(th1 / PI * STEPS_PER_CIRCLE / 2) ;
  pos2 = round(th2 / PI * STEPS_PER_CIRCLE / 2);
}

/*
  Robbo1 8/June/2015
  
  Fixed loop test where the movement may not have actually stopped
  
  Sympton  - The movement would stop sometimes one step short because of floating point values 
             not always the exact amount and 'N' additions of 'N' segments may not add up to 
         the whole.  The best way is to loop until all steps have been done.
         
  Solution - Change the loop finish test from 'i<maxD' to '(posA!=tarA)||(posB!=tarB)'
             That is test for movement not yet finished
         This is a miniminal change to enable the least changes to the code
         
*/
/************** calculate movements ******************/
//#define STEPDELAY_MIN 200 // micro second
//#define STEPDELAY_MAX 1000
long stepAuxDelay = 0;
int stepdelay_min = 200;
int stepdelay_max = 2000;
#define ACCELERATION 2 // mm/s^2 don't get inertia exceed motor could handle
#define SEGMENT_DISTANCE 10 // 1 mm for each segment
#define SPEED_STEP 1


void doMove() {
  long mDelay = stepdelay_max;
  long temp_delay;
  int speedDiff = -SPEED_STEP;
  int dA, dB, maxD;
  float stepA, stepB, cntA = 0, cntB = 0;
  int d;
  dA = tarA - posA;
  dB = tarB - posB;
  maxD = max(abs(dA), abs(dB));
  stepA = (float) abs(dA) / (float) maxD; // 1 or 1 ??????
  stepB = (float) abs(dB) / (float) maxD; // 1 or 1 ??????
  //Serial.printf("move: max:%d da:%d db:%d\n",maxD,dA,dB);
  //Serial.print(stepA);Serial.print(' ');Serial.println(stepB);
  //for(int i=0;i<=maxD;i++){
  //for(int i=0;i<maxD;i++){                                           // Robbo1 2015/6/8 Removed - kept for now to show what the loop looked like before
  for (int i = 0; (posA != tarA) || (posB != tarB); i++) {                         // Robbo1 2015/6/8 Changed - change loop terminate test to test for moving not finished rather than a preset amount of moves
    //Serial.printf("step %d A:%d B;%d\n",i,posA,posB);
    // move A
    if (posA != tarA) {
      cntA += stepA;
      if (cntA >= 1) {
        d = dA > 0 ? motorAfw : motorAbk;
        posA += (dA > 0 ? 1 : -1);
        stepperMoveA(d);
        cntA -= 1;
      }
    }
    // move B
    if (posB != tarB) {
      cntB += stepB ;
      if (cntB >= 1) {
        d = dB > 0 ? motorBfw : motorBbk ;
        posB += (dB > 0 ? 1 : -1) ;
        stepperMoveB(d);
        cntB -= 1;
      }
    }
    mDelay = constrain(mDelay + speedDiff, stepdelay_min, stepdelay_max);
    temp_delay = mDelay + stepAuxDelay;
    if (millis() - last_time > 400) {
      last_time = millis();
      if (true == process_serial()) {
        return;
      }
    }
    if (temp_delay > stepdelay_max) {
      temp_delay = stepAuxDelay;
      delay(temp_delay / 1000);
      delayMicroseconds(temp_delay % 1000);
    }
    else {
      delayMicroseconds(temp_delay);
    }
    if ((maxD - i) < ((stepdelay_max - stepdelay_min) / SPEED_STEP)) {
      speedDiff = SPEED_STEP;
    }
  }
  // Serial.printf("finally %d A:%d B;%d\n",maxD,posA,posB);
  posA = tarA;
  posB = tarB;
}


void prepareMove() {
  int maxD;
  unsigned long t0, t1;
  float segInterval;
  float dx = tarX - curX;
  float dy = tarY - curY;
  float distance = sqrt(dx * dx + dy * dy);
  float distanceMoved = 0, distanceLast = 0;
  //Serial.print("distance=");Serial.println(distance);
  //Serial.print(tarX);Serial.print(' ');Serial.println(tarY);
  if (distance < 0.001) 
    return;
  scaraInverseKinect(tarX, tarY);
  thetaToSteps(th1, th2);
  tarA = pos1; tarB = pos2;
  //Serial.print("theta:");Serial.print(th1/PI*180);Serial.print(' ');Serial.println(th2/PI*180);
  //Serial.printf("tar Pos %d %d\r\n",tarA,tarB);
  doMove();
  curX = tarX;
  curY = tarY;
}


void initPosition() {
  curX =-(roboSetup.data.arm0len + roboSetup.data.arm1len - 0.01); curY = 0;
  scaraInverseKinect(curX, curY);
  curTh1 = th1; curTh2 = th2;
  thetaToSteps(curTh1, curTh2);
  posA = pos1;
  posB = pos2;
}


/************** calculate movements ******************/
void parseCordinate(char * cmd) {
  char * tmp;
  char * str;
  str = strtok_r(cmd, " ", &tmp);             // Robbo1 2015/6/8 comment - this removes the G code token from the input string - potential for future errors if method of processing G codes changes
  while((str = strtok_r(0, " ", &tmp)) != NULL) {  // Robbo1 2015/6/8 changed - placed strtok_r into loop test so that the pointer tested is the one used in the current loop
    //str = strtok_r(0, " ", &tmp);           // Robbo1 2015/6/8 removed - removed from here and place in the while loop test
    //Serial.printf("%s;",str);
    if (str[0] == 'X') {
      tarX = atof(str + 1);
    } else if (str[0] == 'Y') {
      tarY = atof(str + 1);
    } else if (str[0] == 'Z') {
      tarZ = atof(str + 1);
    } else if (str[0] == 'F') {
      float speed = atof(str + 1);
      tarSpd = speed / 60; // mm/min -> mm/s
    } else if (str[0] == 'A') {
      stepAuxDelay = atol(str + 1);
    }
  }

  if (!spotDraw) prepareMove();
  else {
    servoPen.write(roboSetup.data.penUpPos);
    prepareMove();
    servoPen.write(roboSetup.data.penDownPos);
  }
}


void parseServo(char * cmd) {
  char * tmp;
  char * str;
  str = strtok_r(cmd, " ", &tmp);
  int pos = atoi(tmp);
  servoPen.write(pos);
}


void parseAuxDelay(char * cmd) {
  char * tmp;
  char * str;
  str = strtok_r(cmd, " ", &tmp);
  stepAuxDelay = atol(tmp);
}


void parseLaserPower(char * cmd) {
  char * tmp;
  char * str;
  str = strtok_r(cmd, " ", &tmp);
  int pwm = atoi(tmp);
  laser.run(pwm);
}


void parseGcode(char * cmd) {
  int code;
  code = atoi(cmd);
  switch (code) {
    case 1 : // xyz move
      parseCordinate(cmd);
      break;
    case 27 :
      brushClean(false, false);
      break;
    case 28 : // home
      goHome();
      break; 
    case 29 : // Check color pos
      tarX = colorPoint[17][0];
      tarY = colorPoint[17][1];
      prepareMove();

      servoPen.write(roboSetup.data.penDownPos);
      delay(1000);

      servoPen.write(roboSetup.data.penUpPos);
      delay(100);

      tarX = colorPoint[0][0];
      tarY = colorPoint[0][1];
      prepareMove();

      servoPen.write(roboSetup.data.penDownPos);
      delay(1000);

      servoPen.write(roboSetup.data.penUpPos);
      delay(100);
      break; 
    case 30 :
      spotDraw = true;
  }
}


void goHome() {
  Serial.println("Move to start point start");
  tarX =-(roboSetup.data.arm0len + roboSetup.data.arm1len - 0.01); 
  tarY = 0;
  prepareMove();
  Serial.println("Move to start point complete");
  servoPen.write(roboSetup.data.penUpPos + 10);
}


void brushClean(bool powerUp, bool noSponge) {

  int waterCnt = 20;
  if (powerUp) {
    waterCnt = 40;
  }

  Serial.println("Watering Brush start");
  tarX = waterPoint[0]; tarY = waterPoint[1];
  prepareMove();
  servoPen.write(roboSetup.data.penDownPos);
  delay(100);
  for (int j = 0; j < waterCnt; j++){
    servoPen.write(roboSetup.data.penUpPos);
    delay(100);
    servoPen.write(roboSetup.data.penDownPos);
    delay(100);
  }
  Serial.println("Watering Brush complete");
  servoPen.write(roboSetup.data.penUpPos);

  if (noSponge) {
    Serial.println("No Sponge Time");
    return;
  }

  Serial.println("Removing water start");

  tarX = spongePoint[random(3)][0]; tarY = spongePoint[random(3)][1];
  prepareMove();
  for (int i = 0; i < 7; i++){
    servoPen.write(roboSetup.data.penUpPos);
    delay(100);
    servoPen.write(roboSetup.data.penDownPos);                                                                            
    delay(100);
  }
  Serial.println("Removing water complete");
  servoPen.write(roboSetup.data.penUpPos);

  Serial.println("Watering Brush start : Second");
  tarX = waterPoint[0]; tarY = waterPoint[1];
  prepareMove();
  servoPen.write(roboSetup.data.penDownPos);
  delay(100);
  for (int j = 0; j < waterCnt; j++){
    servoPen.write(roboSetup.data.penUpPos);
    delay(100);
    servoPen.write(roboSetup.data.penDownPos);
    delay(100);
  }
  Serial.println("Watering Brush complete : Second");
  servoPen.write(roboSetup.data.penUpPos);
}


void brushColor(int colorPos) {
  delay(100);
  servoPen.write(180);
  delay(100);
  Serial.print("Coloring Brush start : "); Serial.println((int)colorPos);
  tarX = colorPoint[colorPos][0];
  tarY = colorPoint[colorPos][1];
  prepareMove();

  servoPen.write(roboSetup.data.penDownPos);
  tarX -= 5;
  prepareMove();
  tarY -= 5;
  prepareMove();
  for (int i = 0; i < 7; i++) {
    tarX += 10;
    prepareMove();
    tarY += 10;
    prepareMove();
    tarX -= 10;
    prepareMove();
    tarY -= 10;
    prepareMove();
  }
  Serial.print("Coloring Brush complete : "); Serial.println((int)colorPos);
  delay(100);
  servoPen.write(180);
  delay(100);
}


void parseCcode(char * cmd) {
  char * tmp;
  char * str;
  str = strtok_r(cmd, " ", &tmp);
  int colorPos = atoi(tmp);
  bool powerUp = false;
  bool noSponge = false;

  if (prevColorPos == 0 || prevColorPos == 1 || prevColorPos == 2|| prevColorPos == 10) powerUp = true;
  if (prevColorPos == colorPos) noSponge = true;
  
  brushClean(powerUp, noSponge); 
  brushColor(colorPos);

  prevColorPos = colorPos;
}


void echoArmSetup(char * cmd) {
  Serial.print("M10 MSCARA ");
  Serial.print(roboSetup.data.arm0len); Serial.print(' ');
  Serial.print(roboSetup.data.arm1len); Serial.print(' ');
  Serial.print(curX); Serial.print(' ');
  Serial.print(curY); Serial.print(' ');
  Serial.print("A"); Serial.print((int)roboSetup.data.motoADir);
  Serial.print(" B"); Serial.print((int)roboSetup.data.motoBDir);
  Serial.print(" S"); Serial.print((int)roboSetup.data.speed);
  Serial.print(" U"); Serial.print((int)roboSetup.data.penUpPos);
  Serial.print(" D"); Serial.println((int)roboSetup.data.penDownPos);
}


void parseRobotSetup(char * cmd) {
  char * tmp;
  char * str;
  str = strtok_r(cmd, " ", &tmp);
  while(str != NULL){
    str = strtok_r(0, " ", &tmp);
    if (str[0] == 'A') {
      roboSetup.data.motoADir = atoi(str + 1);
      //Serial.print("motorADir ");Serial.print(roboSetup.data.motoADir);
    } else if (str[0] == 'B') {
      roboSetup.data.motoBDir = atoi(str + 1);
      //Serial.print("motoBDir ");Serial.print(roboSetup.data.motoBDir);
    } else if (str[0] == 'M') {
      roboSetup.data.arm0len = atoi(str + 1);
      //Serial.print("ARML1 ");Serial.print(roboSetup.data.arm0len);
    } else if (str[0] == 'N') {
      roboSetup.data.arm1len = atoi(str + 1);
      //Serial.print("ARML2 ");Serial.print(roboSetup.data.arm1len);
    } else if (str[0] == 'D') {
      roboSetup.data.speed = atoi(str + 1);
      //Serial.print("Speed ");Serial.print(roboSetup.data.speed);
    }
  }
  syncRobotSetup();
}


void parsePenPosSetup(char * cmd) {
  char * tmp;
  char * str;
  str = strtok_r(cmd, " ", &tmp);
  while(str != NULL){
    str = strtok_r(0, " ", &tmp);
    if(str[0] == 'U'){
      roboSetup.data.penUpPos = atoi(str + 1);
    }else if(str[0] == 'D'){
      roboSetup.data.penDownPos = atoi(str + 1);    
    }
  }
  Serial.print("M2 U:");
  Serial.print(roboSetup.data.penUpPos);
  Serial.print(" D:");
  Serial.print(roboSetup.data.penDownPos);

  syncRobotSetup();
}


void parseMcode(char * cmd) {
  int code;
  code = atoi(cmd);
  switch(code){
    case 1:
      parseServo(cmd);
      break;
    case 2: // set pen position
      parsePenPosSetup(cmd);
      break;
    case 3:
      parseAuxDelay(cmd);
      break;
    case 4:
      parseLaserPower(cmd);
      break;
    case 5:
      parseRobotSetup(cmd);
      break;
    case 10: // echo robot config
      echoArmSetup(cmd);
      break;
  }
}


void parseCmd(char * cmd) {
  if (cmd[0] == 'G') { // gcode
    parseGcode(cmd + 1);  
  } else if (cmd[0] == 'M') { // mcode
    parseMcode(cmd + 1);
  } else if (cmd[0] == 'P') {
    Serial.print("POS X"); Serial.print(curX); Serial.print(" Y"); Serial.println(curY);
  } else if (cmd[0] == 'C') {
    parseCcode(cmd + 1);
  }
  Serial.println("OK");
}


// local data
void initRobotSetup() {
  //Serial.println("read eeprom");
  for (int i = 0; i < 64; i++) {
    roboSetup.buf[i] = EEPROM.read(i);
  }

  Serial.println("set to default setup");
  // set to default setup
  memset(roboSetup.buf, 0, 64);
  memcpy(roboSetup.data.name, "SCARA4", 6);
  roboSetup.data.motoADir = 0;
  roboSetup.data.motoBDir = 0;
  roboSetup.data.arm0len = ARML1;
  roboSetup.data.arm1len = ARML2;
  roboSetup.data.speed = 80;
  roboSetup.data.penUpPos = 180;
  roboSetup.data.penDownPos = 120;
  roboSetup.data.spongePos = 120;
  syncRobotSetup();

  // init motor direction
  if (roboSetup.data.motoADir == 0) {
    motorAfw = 1; motorAbk = -1;
  } else {
    motorAfw = -1; motorAbk = 1;
  }
  if (roboSetup.data.motoBDir == 0) {
    motorBfw = 1; motorBbk = -1;
  } else {
    motorBfw = -1; motorBbk = 1;
  }
  int spd = 100 - roboSetup.data.speed;
  stepdelay_min = spd * 10;
  stepdelay_max = spd * 100;
  //Serial.printf("spd %d %d\n",stepdelay_min,stepdelay_max);
}


void syncRobotSetup() {
  int i;
  for (i = 0; i < 64; i++) {
    EEPROM.write(i, roboSetup.buf[i]);
  }
}


/************** arduino ******************/
void setup() {
  Serial.begin(115200);
  initRobotSetup();
  servoPen.attach(servopin);
  servoPen.write(roboSetup.data.penUpPos);
  initPosition();
  Serial.print("Target X : "); Serial.println((int)tarX);
  Serial.print("Target Y : "); Serial.println((int)tarY);
  Serial.print("Current X : "); Serial.println((int)curX);
  Serial.print("Current Y : "); Serial.println((int)curY);
}


char buf[64];
char bufindex;
char buf2[64];
char bufindex2;


boolean process_serial(void) {
  boolean result = false;
  memset(buf, 0, 64);
  bufindex = 0;
  while (Serial.available()) {
    char c = Serial.read();
    buf[bufindex++] = c; 
    if (c == '\n') {
      buf[bufindex] = '\0';
      parseCmd(buf);
      result = true;
      memset(buf, 0, 64);
      bufindex = 0;
    }
    if (bufindex >= 64) {
      bufindex = 0;
    }
  }
  return result;
}

/*
  Robbo1 8/June/2015
  
  Fixed potential probelms from buffer overflow and first cmd string not being null terminated
  
*/

void loop() {
  if(Serial.available()) {
    char c = Serial.read();
    //buf[bufindex++]=c;                   // Robbo1 2015/6/8 Removed - Do not store the \n
    if(c == '\n') {
      buf[bufindex++] = '\0';              // Robbo1 2015/6/8 Add     - Null terminate the string - Essential for first use of 'buf' and good programming practice
      parseCmd(buf);
      memset(buf, 0, 64);
      bufindex = 0;
    } else if(bufindex < 64) {             // Robbo1 2015/6/8 Add     - Only add char to string if the string can fit it and still be null terminated 
      buf[bufindex++] = c;                 // Robbo1 2015/6/8 Moved   - Store the character here now
    }
  }
}