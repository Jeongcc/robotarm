import sys
import os
import time
from xml.dom import minidom
from PyQt5.QtGui import*
from PyQt5.QtWidgets import *
from PyQt5.QtCore import *
from RobotUtils import *
from math import *
import inspect
import ast
import re


def buildBezierSegment(p0,p1,p2,p3):
    segList = []
    px = p0[0]
    py = p0[1]
    #print "bez",p0,p1,p2,p3
    for i in range(1,100):
        ratio = float(i)/100
        x00=p0[0]+(p1[0]-p0[0])*ratio;y00=p0[1]+(p1[1]-p0[1])*ratio
        x01=p1[0]+(p2[0]-p1[0])*ratio;y01=p1[1]+(p2[1]-p1[1])*ratio
        x02=p2[0]+(p3[0]-p2[0])*ratio;y02=p2[1]+(p3[1]-p2[1])*ratio
        x10=(x01-x00)*ratio+x00;
        y10=(y01-y00)*ratio+y00;
        x11=(x02-x01)*ratio+x01;
        y11=(y02-y01)*ratio+y01;
        x20=(x11-x10)*ratio+x10;
        y20=(y11-y10)*ratio+y10;
        dx = x20-px;
        dy = y20 - py;
        dis = sqrt(dx*dx+dy*dy)
        if dis>1:
            segList.append((x20,y20))
            px=x20;py=y20;
    if len(segList)==0:
        segList.append((p3[0],p3[1]))
    return segList


def buildQuadraticBezierSegment(p0, p1, p2):
    segList = []
    currentSegmentX = p0[0]
    currentSegmentY = p0[1]

    for i in range(1,100):
        t = float(i)/100
        curvePointX = (1 - t) * (1 - t) * p0[0] + 2 * (1 - t) * t * p1[0] + t * t * p2[0];
        curvePointY = (1 - t) * (1 - t) * p0[1] + 2 * (1 - t) * t * p1[1] + t * t * p2[1];
        dis = sqrt( (curvePointX - currentSegmentX) ** 2 + (curvePointY - currentSegmentY) ** 2)
        if dis > 1:
            segList.append((curvePointX, curvePointY))
            currentSegmentX = curvePointX;
            currentSegmentY = curvePointY;

    if len(segList) == 0:
        segList.append(p2[0], p2[1])
    return segList


def buildArcSegment(rx,ry,phi,fA,fS,x1,y1,x2,y2):
    # fA: large arc flag
    # fS: sweep flag
    segList=[]
    # calc center for ellipse
    #print "from",x1,y1,x2,y2
    phi = phi/180*pi
    x1p = cos(phi)*(x1-x2)/2+sin(phi)*(y1-y2)/2
    y1p = -sin(phi)*(x1-x2)/2+cos(phi)*(y1-y2)/2
    lam = x1p*x1p/(rx*rx) + y1p*y1p/(ry*ry)
    if lam > 1:
        rx = sqrt(lam) * rx
        ry = sqrt(lam) * ry
    
    # fix for math domain error
    tmp = (rx*rx*ry*ry-rx*rx*y1p*y1p-ry*ry*x1p*x1p)/(rx*rx*y1p*y1p+ry*ry*x1p*x1p)
    st = sqrt(round(tmp,5))
    if fA == fS:
        cp_sign =- 1
    else:
        cp_sign = 1
    cxp = cp_sign * (st * rx * y1p / ry)
    cyp = cp_sign * (-st * ry * x1p / rx)
    cx = cos(phi) * cxp - sin(phi) * cyp + (x1 + x2) / 2
    cy = sin(phi) * cxp + cos(phi) * cyp + (y1 + y2)/2
    #print "cent",cx,cy
    
    Vxc = (x1p - cxp) / rx
    Vyc = (y1p - cyp) / ry
    Vxc = (x1p - cxp) / rx
    Vyc = (y1p - cyp) / ry
    Vxcp = (-x1p-cxp) / rx
    Vycp = (-y1p-cyp) / ry
    
    if Vyc >= 0:
        cp_sign = 1
    else:
        cp_sign =- 1
    th1 = cp_sign * acos(Vxc / sqrt(Vxc * Vxc + Vyc * Vyc)) / pi * 180
    
    if (Vxc * Vycp - Vyc * Vxcp) >= 0:
        cp_sign = 1
    else:
        cp_sign =- 1
    tmp = (Vxc * Vxcp + Vyc * Vycp) / (sqrt(Vxc * Vxc + Vyc * Vyc) * sqrt(Vxcp * Vxcp + Vycp * Vycp))
    dth = cp_sign * acos(round(tmp, 3)) / pi * 180
    #if fA>=1:
    #    dth=360-dth
    if fS == 0 and dth > 0:
        dth -= 360
    elif fS >= 1 and dth < 0:
        dth += 360
    
    #print "angle",th1,dth
    
    # build route
    theta = th1 / 180 * pi
    px = rx * cos(theta) + cx
    py = ry * sin(theta) + cy
    for i in range(1, 101) :
        ratio = float(i) / 100
        theta = (th1 + dth * ratio) / 180 * pi
        x = cos(phi) * rx * cos(theta) - sin(phi) * ry * sin(theta) + cx
        y = sin(phi) * rx * cos(theta) + cos(phi) * ry * sin(theta) + cy
        dx = x - px; dy = y - py;
        dis = sqrt(dx * dx + dy * dy)
        if dis > 1 :
            segList.append((x, y))
            px = x; py = y;
    return segList
    

class TxtParser():
    def __init__(self, filename, scene, scale=(1,1)):
        self.pathList = []
        self.originPathList = []
        self.ptrList = []
        self.tmpPath = None
        self.xbias = 0
        self.ybias = 0
        self.pathLen = 0
        self.whratio = 1
        self.scene = scene
        self.scale = scale
        self.tf = []
        self.usertf = [1,0,0,1,0,0]
        self.parse(filename)
    
    # tranform matrix = [ a c e ]
    #                   [ b d f ]
    def moveTo(self, x, y) :
        for i in range(len(self.tf)):
            tf = self.tf[-1-i]
            x1 = tf[0] * x + tf[2] * y + tf[4]
            y1 = tf[1] * x + tf[3] * y + tf[5]
            x = x1
            y = y1

        initpoint = [(x,y)]
        self.originPathList.append(initpoint)
    
    def lineTo(self, x, y):
        for i in range(len(self.tf)):
            tf = self.tf[-1-i]
            x1 = tf[0] * x + tf[2] * y + tf[4]
            y1 = tf[1] * x + tf[3] * y + tf[5]
            x = x1
            y = y1

        point = (x, y)
        self.originPathList[-1].append(point)
    
    def plotToScene(self):
        self.ptrList = []
        for line in self.pathList:
            tmpPath = QPainterPath()
            for i in range(len(line)):
                point = line[i]
                if i==0:
                    tmpPath.moveTo(point[0],point[1])
                else:
                    tmpPath.lineTo(point[0],point[1])
            pen = QPen(QColor(0, 0, 0))
            ptr = self.scene.addPath(tmpPath, pen = pen)
            self.ptrList.append(ptr)

    def resize(self, drawRect = (150, 150, 150, 150)) :
        #self.pathList = copy.deepcopy(self.originPathList)
        self.pathList = []
        self.pathLen = 0
        
        # avoid the deep copy
        firstPath = [(0,0)]
        finalPath = [(1575.0, 1050.0)]
        self.pathList.append(firstPath)
        for p in self.originPathList :
            self.pathList.append(list(p))
        self.pathList.append(finalPath)

        # user define transform
        print("Resize pathList", len(self.pathList))
        for i in range(len(self.pathList)) :
            for j in range(len(self.pathList[i])) :
                x = self.pathList[i][j][0]
                y = self.pathList[i][j][1]
                x1 = self.usertf[0] * x + self.usertf[2] * y + self.usertf[4]
                y1 = self.usertf[1] * x + self.usertf[3] * y + self.usertf[5]
                self.pathList[i][j] = (x1, y1)
        
        (x, y) = self.pathList[0][0]
        (x0, y0) = (x, y)
        xmin = x * self.scale[0]
        xmax = x * self.scale[0]
        ymin = y * self.scale[1]
        ymax = y * self.scale[1]
        # find max min pos on x and y
        for line in self.pathList:
            for p in line:
                x = p[0] * self.scale[0]
                y = p[1] * self.scale[1]
                tmpdx = x - x0
                tmpdy = y - y0
                self.pathLen += sqrt(tmpdx * tmpdx + tmpdy * tmpdy)
                (x0, y0) = (x, y)
                if x < xmin :
                    xmin = p[0]
                if x > xmax :
                    xmax = p[0]
                if y < ymin :
                    ymin = p[1]
                if y > ymax :
                    ymax = p[1]
        #print "size",xmin,ymin,xmax,ymax
        dx = xmax - xmin
        dy = ymax - ymin
        self.whratio = dx / dy
        scaler = min(drawRect[2] / dx, drawRect[3] / dy)

        for i in range(len(self.pathList)) :
            for j in range(len(self.pathList[i])) :
                x = self.pathList[i][j][0] * self.scale[0]
                y = self.pathList[i][j][1] * self.scale[1]
                x = (x - xmin) * scaler + drawRect[0]                    
                y = (y - ymin) * scaler + drawRect[1]
                self.pathList[i][j] = (x, y)
        self.pathList.pop(0) 
        self.pathList.pop()
        return (dx * scaler, dy * scaler)
    
    # stretch for eggbot surface curve
    # eq: x^2/a^2+y^2/b^2 = 1
    # todo: apply a real egg shape equation: http://www.mathematische-basteleien.de/eggcurves.htm
    # http://www.geocities.jp/nyjp07/Egg/index_egg_E.html
    def stretch(self,ycent,h,da=20):
        a = h+da
        for i in range(len(self.pathList)):
            for j in range(len(self.pathList[i])):
                (x,y) = self.pathList[i][j]
                y0=y-ycent
                x0 = h-sqrt(1-y0*y0/a/a)*h
                x = x+x0
                self.pathList[i][j] = (x,y)
  
            
    # def parse(self, filename):
    #     f = open(filename, 'rt') 
    #     lines = f.readlines()
    #     f.close()

    #     # characters = "[]"
    #     # for x in range(len(characters)):
    #     #     lines[0] = lines[0].replace("[","")
    #     lines[0] = lines[0].replace("[", "")
    #     lines[0] = lines[0].replace("]", "")
    #     lines[0] = ''.join(lines[0].split())
    #     self.colorList = lines[0].split(',')
    #     self.originPathList = ast.literal_eval(lines[1])

    def parse(self, filename):
        f = open(filename, 'rt') 
        lines = f.readlines()
        f.close()

        # characters = "[]"
        # for x in range(len(characters)):
        #     lines[0] = lines[0].replace("[","")
        lines[0] = lines[0].replace("[", "")
        lines[0] = lines[0].replace("]", "")
        lines[0] = ''.join(lines[0].split())
        self.colorList = lines[0].split(',')
        self.originPathList = ast.literal_eval(lines[1])

        newOriginPathList = []
        for line in self.originPathList :
            newLists = []
            for coor in line :
                newCoor = ((coor[0] - 600) * 4, (coor[1] - 300) * 4)
                newLists.append(newCoor)
            newOriginPathList.append(newLists)
        self.originPathList = newOriginPathList

if __name__ == '__main__':
    buildArcSegment(10, 10, 0, 0, 10, 10, 0)
    
    
