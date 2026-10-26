#!/usr/bin/env python3
"""80-digit exploratory scan of literal2405.13618 definitions; no proof/credit."""
from pathlib import Path
import json,mpmath as m
m.mp.dps=80
T=[m.mpf(i)/100 for i in range(1,101)]+[m.mpf(i)/10 for i in range(11,301)]+[m.mpf(i) for i in range(31,201)]+[m.mpf(300),m.mpf(500),m.mpf(1000)]

def logB(p,u,v):
 if p==0:return (u+v)/2
 d=(v-u)/2
 return (u+v)/2+m.log(m.cosh(p*d))/p

def logM(kind,u,v,alpha=None):
 a=(u+v)/2;d=abs(v-u)/2
 if d==0:return a
 if kind=='M4':z=m.sqrt(2)*m.sinh(d)/m.asinh(m.sqrt(2)*d)
 elif kind=='M2':z=m.sqrt(2)*m.sinh(d)/m.atan(m.sqrt(2)*d)
 elif kind=='L':z=m.sinh(d)/d if alpha==0 else 2*alpha*m.sinh(d)/m.sinh(2*alpha*d)
 elif kind=='S':z=m.sinh(d)/d if alpha==0 else alpha*m.sinh(d)/m.atan(m.tanh(alpha*d))
 return a+m.log(z)

def scan(kind,p,q,alpha=None):
 vals=[]
 for t in T:
  u=-t;v=t;n=logB(q,u,v)
  delta=logM(kind,u,v,alpha)-logB(p,logM(kind,u,n,alpha),logM(kind,n,v,alpha))
  vals.append((delta,t))
 lo=min(vals);hi=max(vals)
 return {'kind':kind,'alpha':str(alpha),'p':str(p),'q':str(q),'points':len(T),'min_log_difference':list(map(str,lo)),'max_log_difference':list(map(str,hi)),'sign_changes':sum(x[0]*y[0]<0 for x,y in zip(vals,vals[1:]))}

out=[]
for sg in [1,-1]:
 q=(3+sg*m.sqrt(21))/2;out.append(scan('M4',3-2*q,q))
 q=(5+sg*m.sqrt(17))/2;out.append(scan('M2',5-2*q,q))
 for a in [m.mpf(k)/20 for k in range(1,10)]:
  p=sg*m.sqrt(1+16*a*a-16*a**4);q=(1-p)/2-2*a*a;out.append(scan('L',p,q,a))
 for a in [m.sqrt(2+m.sqrt(3))/2,m.sqrt(2-m.sqrt(3))/2]:
  p=sg*m.sqrt((1-12*a*a+112*a**4-64*a**6)/(1+4*a*a));q=(1-p)/2+2*a*a;out.append(scan('S',p,q,a))
Path(__file__).with_name('stabilization-scan.json').write_text(json.dumps({'precision':80,'results':out,'qualification':'Numerical evidence only; no rigorous proof, novelty or discovery credit.'},indent=2)+'\n')
for row in out:print(row)
