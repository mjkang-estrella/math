import json,pathlib,math,itertools,sys
D=pathlib.Path(__file__).resolve().parents[1]
src=(D/'scripts/sixj.py').read_text();exec('def S'+src.split('def S',1)[1].split("if mode=='strip':",1)[0])
from sympy.physics.wigner import wigner_6j
from sympy import Rational
count=0
for k in range(2,16):
 for n in range(k,k+30):
  a=S(k,n);b=wigner_6j(k,k,k,Rational(n,2),Rational(n,2),Rational(n,2));assert (a>0)-(a<0)==(int(bool(b>0))-int(bool(b<0)));count+=1
print('exact Sympy Wigner sign cross-check pairs',count)
