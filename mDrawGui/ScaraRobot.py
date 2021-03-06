import queue
import time
from mDraw import *
from ScaraGui import *

from PyQt5.QtGui import*
from PyQt5.QtWidgets import *
from PyQt5.QtCore import *

from math import *
import ScaraSetup
from RobotUtils import *

def getDegree(theta):
    ang = (theta[0] / pi * 180, theta[1] / pi * 180)
    return ang

def sliceSegment(x, y, tarX, tarY) :
    segList = []
    dx = tarX - x
    dy = tarY - y
    maxD = max(abs(dx), abs(dy))
    maxSteps = int(ceil(maxD)) # 1:1mm per segment, 2:0.5mm

    if maxSteps == 0 :
        return []

    dxStep = float(dx) / maxSteps
    dyStep = float(dy) / maxSteps

    for i in range(0, maxSteps + 1) :
        segList.append((x + dxStep * i, y + dyStep * i))

    return segList[1:]
    
class RobotSetupUI(QWidget):
    def __init__(self,uidialog,robot):
        super(RobotSetupUI, self).__init__()
        self.ui = uidialog()
        self.ui.setupUi(self)
        self.robot = robot
        self.setWindowTitle('Scara Setup')
        self.updateUI()
        self.ui.motoA_CK.mousePressEvent = self.setMotorAck
        self.ui.motoA_CCK.mousePressEvent = self.setMotorAcck
        self.ui.motoB_CK.mousePressEvent = self.setMotorBck
        self.ui.motoB_CCK.mousePressEvent = self.setMotorBcck
        self.ui.btnOk.clicked.connect(self.applySetup)
        self.ui.slidSpeed.valueChanged.connect(self.updateSpeed)
        self.show()
        
    def updateUI(self):
        self.ui.lineArm0.setText(str(self.robot.L1))
        self.ui.lineArm1.setText(str(self.robot.L2))
        if self.robot.motoADir == 0:
            self.ui.motoA_CK.setStyleSheet(motorSelectedStyle)
            self.ui.motoA_CCK.setStyleSheet("")
        else:
            self.ui.motoA_CK.setStyleSheet("")
            self.ui.motoA_CCK.setStyleSheet(motorSelectedStyle)
        if self.robot.motoBDir == 0:
            self.ui.motoB_CK.setStyleSheet(motorSelectedStyle)
            self.ui.motoB_CCK.setStyleSheet("")
        else:
            self.ui.motoB_CK.setStyleSheet("")
            self.ui.motoB_CCK.setStyleSheet(motorSelectedStyle)
        self.ui.labelSpeed.setText("Speed (%d%%)" %(self.robot.speed))
        self.ui.slidSpeed.setValue(self.robot.speed)

    def updateSpeed(self,value):
        self.ui.labelSpeed.setText("Speed (%d%%)" % (value))
        self.robot.speed = value

    def applySetup(self):
        self.robot.L1 = float(str(self.ui.lineArm0.text()))
        self.robot.L2 = float(str(self.ui.lineArm1.text()))
        self.robot.M5()
        self.hide()
        self.robot.initRobotCanvas()

    def setMotorAck(self,event):
        self.robot.motoADir = 0
        self.updateUI()

    def setMotorAcck(self,event):
        self.robot.motoADir = 1
        self.updateUI()
        
    def setMotorBck(self,event):
        self.robot.motoBDir = 0
        self.updateUI()

    def setMotorBcck(self, event):
        self.robot.motoBDir = 1
        self.updateUI()

class Scara(QGraphicsItem):
    def __init__(self, scene, ui, parent = None):
        super(Scara, self).__init__(parent)
        self.robotState = IDLE
        self.mode = IDLE
        self.scene = scene
        self.ui = ui
        self.color = QColor(QtCore.Qt.lightGray)
        # Arm Length
        self.L1 = 248.0
        self.L2 = 206.0
        self.speed = 50
        self.scaler = 1.0
        self.motoADir = 0
        self.motoBDir = 0
        self.pos = (-(self.L1 + self.L2 - 0.01), 0.0)
        #self.pos=(-200.0,0.0)
        # theta1 and 2 in clock wise direction
        self.th = self.scaraInverseKinect(self.pos)
        self.q = queue.Queue()
        #print "theta",self.th
        self.moving = False
        self.laserMode = False
        self.laserPower = 0.0
        self.robotCent = None
        self.sendCmd = None
        self.moveList = None
        self.colorList = None
        self.pEllipse0 = None
        self.pEllipse1 = None
        self.moveList = None
        self.printing = False
        self.pausing = False
        self.laserBurnDelay = 0
        self.lastx = 0
        self.lasty = 0
        self.ui.label.setText("X(mm)")
        self.ui.label_2.setText("Y(mm)")
        
    def boundingRect(self):
        return QRectF(0,0,100,100)
        
    def initRobotCanvas(self):
        if self.pEllipse0 != None :
            self.scene.removeItem(self.pEllipse0)
            self.scene.removeItem(self.pEllipse1)
        pen = QPen(QColor(124, 124, 124))
        pen.setStyle(Qt.DashDotLine)
        self.pEllipse0 = self.scene.addEllipse(self.robotCent[0] - self.L1, self.robotCent[1] - self.L1, self.L1 * 2, self.L1 * 2, pen = pen)
        pen = QPen(QColor(124, 124, 124))
        self.pEllipse1 = self.scene.addEllipse(self.robotCent[0] - self.L1-self.L2, self.robotCent[1] - self.L1-self.L2, (self.L1+self.L2)*2,(self.L1+self.L2)*2,pen=pen)
        pTxt = self.scene.addText("O")
        cent = QPointF(self.robotCent[0],self.robotCent[1])
        pTxt.setPos(cent)
        pTxt.setDefaultTextColor(QtCore.Qt.darkGray)
        self.ui.labelScale.setText(str(self.scaler))

    def paint(self, painter, option, widget = None) : # paint??? ????????? ?????? ??????..? => mScara??? ???????????? ?????? ???
        painter.setRenderHint(QPainter.Antialiasing)
        (x1, y1, x2, y2) = self.sceraDirectKinect(self.th)
        
        # qt graph in inverse y direction
        y1 = - y1
        y2 = - y2
        ang = getDegree(self.th)
        
        pen = QPen(QtGui.QColor(124, 124, 124))
        painter.setBrush(QtCore.Qt.darkGray)
        painter.setPen(pen)
        # draw inner arm
        line = QLineF(0,0,x1,y1)
        painter.drawLine(line)
        # draw outer arm
        line = QLineF(x1,y1,x2,y2)
        painter.drawLine(line)
        # draw end nodes
        #painter.setBrush(QtCore.Qt.white)

        painter.drawEllipse(x1-5,y1-5,10,10)
        painter.drawEllipse(x2-5,y2-5,10,10)
        
        pen = QPen(QtGui.QColor(0, 169, 231))
        painter.setBrush(QtGui.QColor(0, 169, 231))
        painter.setPen(pen)
        painter.drawEllipse(-5,-5,10,10)
        """
        painter.drawText(x2-30,y2+10,"(%.2f,%.2f)" %(x2,-y2))
        painter.drawText(-30,10,"%.2f" %(ang[0]))
        painter.drawText(x1-30,y1+30,"%.2f" %(ang[1]))
        # draw arc angle
        painter.setBrush(QtCore.Qt.yellow)
        painter.drawPie(-20,-20,40,40,180*16,-ang[0]*16)
        painter.drawPie(x1-20,y1-20,40,40,(360-ang[0])*16,-ang[1]*16)
        """
        if x2 != self.lastx or y2 != self.lasty :
            self.ui.labelXpos.setText("%.2f" % (x2))
            self.ui.labelYpos.setText("%.2f" % (-y2))
            self.lastx = x2
            self.lasty = y2
        
    def sceraDirectKinect(self, th) :
        L1 = self.L1
        L2 = self.L2
        th1 = th[0]
        th2 = th[1]
        x1 = -L1 * cos(th1)
        y1 = L1 * sin(th1)
        x2 = -L1 * cos(th1) - L2 * cos(th1 + th2 - pi)
        y2 = L1 * sin(th1) + L2 * sin(th1 + th2 - pi)
        return (x1, y1, x2, y2)
    
    def scaraInverseKinect(self, pos) :
        L1 = self.L1
        L2 = self.L2
        x = pos[0]
        y = pos[1]
        # the same as arduino site
        th1 = 2 * atan((2*L1*y + sqrt(-L1*L1*L1*L1 + 2*L1*L1*L2*L2 + 2*L1*L1*x*x + 2*L1*L1*y*y - L2*L2*L2*L2 + 2*L2*L2*x*x + 2*L2*L2*y*y - x*x*x*x - 2*x*x*y*y - y*y*y*y))/(L1*L1 - 2*L1*x - L2*L2 + x*x + y*y));
        th2 = 2 * atan(sqrt((- L1*L1 + 2*L1*L2 - L2*L2 + x*x + y*y)*(L1*L1 + 2*L1*L2 + L2*L2 - x*x - y*y))/(L1*L1 + 2*L1*L2 + L2*L2 - x*x - y*y));
        # change to degree
        # th1 = th1/pi*180
        # th2 = th2/pi*180
        return (th1, th2)
    
    """
    the real movement of scara robot 
    """
    def moveOverList(self) :

        if self.moveList == None : return

        moveLen = len(self.moveList)
        moveCnt = 0
        self.M4(0) # turn laser power down when perform transition
        self.q.get()

        if self.mode == COLOR :
            self.G27()
            self.q.get()

        for move in self.moveList :
            
            if self.mode == COLOR :
                self.C1(self.colorList[moveCnt])
                print("Current Color", self.colorList[moveCnt])
                self.q.get()
            # loop for all points
            lineNode = len(move)
            for i in range(lineNode) :
                p = move[i]
                x = p[0] - self.robotCent[0]
                y = -p[1] + self.robotCent[1] # y in reverse dir from qt graph
                (x1, y1, x2, y2) = self.sceraDirectKinect(self.th)
                # slice into 1mm (1pix = 1mm)
                if i == 0 :
                    segList = [(x, y)]
                else:
                    segList = sliceSegment(x2, y2, x, y)
                for s in segList :
                    try:
                        if self.printing == False :
                            if self.laserMode :
                                self.M4(0) # turn off the laser when the user aborts the printing process
                            return
                        self.waitWhilePaused(self.laserMode and i > 0)
                        self.th = self.scaraInverseKinect((s[0], s[1]))
                        auxDelay = 0
                        if self.laserMode :
                            if i > 0 :
                                auxDelay = self.laserBurnDelay * 1000
                            elif i == 0 :
                                self.M4(0) # turn laser power down when perform transition
                                self.q.get()
                        self.G1(s[0], s[1], auxdelay = auxDelay)
                        while self.robotState == BUSYING :
                            self.q.get()
                    except:
                        pass
                #print "segdone",len(segList)
                # ignore single points (lineNode==1)
                if self.laserMode and i == 0 :
                        self.M4(self.laserPower) # turn laser power back to set value
                        self.q.get()
                if not self.laserMode and i == 0 and lineNode > 1 :
                    self.M1(self.penDownPos)
                    self.q.get()
                    time.sleep(0.2)

            if not self.laserMode :
                self.M1(self.penUpPos)
                self.q.get()
                time.sleep(0.2)

            moveCnt += 1
            self.robotSig.emit("pg %d" % (int(moveCnt * 100 / moveLen)))
        
        if self.mode == COLOR :
            self.G27()
            self.q.get()
        self.G28()
        self.printing = False
        self.robotSig.emit("done")
    
    def printPic(self):
        #update pen servo position
        mStr = str(self.ui.penUpSpin.value())
        self.penUpPos = int(mStr)
        mStr = str(self.ui.penDownSpin.value())
        self.penDownPos = int(mStr)
        value = int(self.ui.slideLaserPower.value())
        laserpwm = value * 255 / 100
        self.laserPower = laserpwm
        
        while not self.q.empty() :
            self.q.get()

        self.printing = True
        self.pausing = False
        self.moveListThread = WorkInThread(self.moveOverList)
        self.moveListThread.setDaemon(True)
        self.moveListThread.start()
        
    def stopPrinting(self) :
        self.printing = False
        self.pausing = False
    
    def pausePrinting(self, v) :
        self.pausing = v
    
    def waitWhilePaused(self, isLaserOn) :
        if self.pausing :
            if isLaserOn :
                self.M4(0) # turn off the laser while the printing is paused
            while self.pausing :
                time.sleep(0.5)
            if isLaserOn :
                self.M4(self.laserPower) # turn on laser when the printing is continued, and it was on before pausing
    
    """
    simulate the actual movement of steppermotor
    """
    def prepareMove(self, target) :
        ""
        target = (target.x(), -target.y())
        dx = target[0] - self.pos[0]
        dy = target[1] - self.pos[1]
        distance = sqrt(dx * dx + dy * dy)
        self.targetTh = self.scaraInverseKinect(target)
        dth1 = self.targetTh[0] - self.th[0]
        dth2 = self.targetTh[1] - self.th[1]
        maxD = max(abs(dth1), abs(dth2))
        moveSteps = maxD / pi * 180 / 2 # in 2 degree, todo: project to real stepper param
        maxStep = ceil(moveSteps)
        self.deltaStep = (dth1 / maxStep, dth2 / maxStep)
        self.maxStep = maxStep
        """
        #print "target",self.targetTh
        print "current angle",getDegree(self.th)
        print "target angle",getDegree(self.targetTh)
        print "delta angle",getDegree((dth1,dth2))
        print "max step",maxStep
        print "steps",self.deltaStep
        """
        
    def parseEcho(self, msg) :
        if "M10" in msg :
            tmp = msg.split()
            if tmp[1] != "MSCARA" : return
            self.L1 = float(tmp[2])
            self.L2 = float(tmp[3])
            pos = (float(tmp[4]), float(tmp[5]))
            if tmp[6] == "A0" :
                self.motoADir = 0
            else :
                self.motoADir = 1
            if tmp[7] == "B0" :
                self.motoBDir = 0
            else :
                self.motoBDir = 1
            if msg.find("S") > -1 :
                self.speed = int(tmp[8][1:])
            if msg.find("U") > -1 :
                self.penUpPos = int(tmp[9][1:])
                self.ui.penUpSpin.setValue(self.penUpPos)
            if msg.find("D") > -1 :
                self.penDownPos = int(tmp[10][1:])
                self.ui.penDownSpin.setValue(self.penDownPos)
            self.th = self.scaraInverseKinect(pos)
            self.initRobotCanvas()
            self.robotState = IDLE

    def robotGoBusy(self) :
        self.robotState = BUSYING
        self.ui.labelMachineState.setText("BUSY")

    def G1(self, x, y, feedrate = 0, auxdelay = None):
        if self.robotState != IDLE : return
        cmd = "G1 X%.2f Y%.2f" % (x, y)
        if auxdelay != None :
            cmd += " A%d" % (auxdelay)
        cmd += '\n'
        self.robotGoBusy()
        self.sendCmd(cmd)
    
    def G27(self) :
        if self.robotState != IDLE : return
        cmd = "G27\n"
        self.robotGoBusy()
        self.sendCmd(cmd)

    def G28(self) :
        if self.robotState != IDLE : return
        cmd = "G28\n"
        self.robotGoBusy()
        self.sendCmd(cmd)
        self.pos = (-(self.L1 + self.L2-0.01), 0.0)
        self.th = self.scaraInverseKinect(self.pos)
    
    def C1(self, color) :
        if self.robotState != IDLE : return
        cmd = "C1 %d\n" % (color)
        self.robotGoBusy()
        self.sendCmd(cmd)
    
    def M1(self, pos) :
        if self.robotState != IDLE : return
        cmd = "M1 %d" % (pos)
        cmd += '\n'
        self.robotGoBusy()
        self.sendCmd(cmd)
        
    def M2(self) :
        if self.robotState != IDLE : return
        posUp = int(self.ui.penUpSpin.value())
        posDown = int(self.ui.penDownSpin.value())
        cmd = "M2 U%d D%d\n" % (posUp, posDown)
        self.robotGoBusy()
        self.sendCmd(cmd)
            
    def M3(self, auxdelay) : # aux delay
        if self.robotState != IDLE : return
        cmd = "M3 %d\n" % (auxdelay)
        self.robotGoBusy()
        self.sendCmd(cmd)
    
    def M4(self, laserPower, rate = 1): # setup laser power
        if self.robotState != IDLE : return
        cmd = "M4 %d\n" % (int(laserPower * rate))
        self.robotGoBusy()
        self.sendCmd(cmd)
    
    def M5(self):
        if self.robotState != IDLE : return
        cmd = "M5 A%d B%d M%d N%d D%d\n" % (self.motoADir, self.motoBDir, self.L1, self.L2, self.speed)
        self.robotGoBusy()
        self.sendCmd(cmd)
        self.robotSig.emit("toggleComPort")
        
    def M10(self) : # read robot arm setup and init pos
        cmd = "M10\n"
        self.sendCmd(cmd)
    
    def moveStep(self):
        while True:
            self.th = (self.th[0] + self.deltaStep[0], self.th[1] + self.deltaStep[1])
            (x1, y1, x2, y2) = self.sceraDirectKinect(self.th)
            time.sleep(0.05)
            self.maxStep -= 1
            
            if self.maxStep == 0 or self.moving == False :
                self.moving = False
                return
        
    def moveTo(self, pos, absolute = False) :
        if self.moving :
            self.moving = False
            self.moveThread.join()
        self.prepareMove(pos)
        self.G1(pos.x(), -pos.y())
        self.moving = True
        self.moveThread = WorkInThread(self.moveStep)
        self.moveThread.setDaemon(True)
        self.moveThread.start()
    
    def showSetup(self):
        self.robotSetup = RobotSetupUI(ScaraSetup.Ui_Dialog,self)
