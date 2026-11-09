import sys,random,math;sys.path.insert(0,'.')
from csc import csc_center
from csc2 import center
from fractions import Fraction as F
random.seed(3);agree=0;tot=0
for t in range(300):
    n=random.randint(4,10);ang=sorted(random.random()*6.283 for _ in range(n))
    r=[1+random.uniform(-.1,.1) for _ in range(n)]
    X=[(F(round(1000*r[i]*math.cos(a))),F(round(1000*r[i]*math.sin(a)))) for i,a in enumerate(ang)]
    if len(set(X))<n: continue
    a=csc_center(X) is None; b=center(X) is None; tot+=1; agree+=(a==b)
print('agree',agree,'of',tot)
