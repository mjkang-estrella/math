"""Exact rational interval exclusion of the explicit Hughston–Salamon Example 10.2.
Original code MIT. Only reads constants; no numerical minimization or author audit.
"""
from fractions import Fraction as F
import json
class I:
    def __init__(self,a,b=None): self.a,self.b=F(a),F(a if b is None else b); assert self.a<=self.b
    def __add__(self,y):
        y=as_i(y);return I(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self): return I(-self.b,-self.a)
    def __sub__(self,y): return self+-as_i(y)
    def __rsub__(self,y):return as_i(y)+-self
    def __mul__(self,y):
        y=as_i(y);v=[self.a*y.a,self.a*y.b,self.b*y.a,self.b*y.b];return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,y):
        y=as_i(y);assert not y.a<=0<=y.b;return self*I(1/y.b,1/y.a)
    def __rtruediv__(self,y):return as_i(y)/self
    def sq(self):return I(0 if self.a<=0<=self.b else min(self.a*self.a,self.b*self.b),max(self.a*self.a,self.b*self.b))
    def show(self):return [str(self.a),str(self.b)]
def as_i(x):return x if isinstance(x,I) else I(x)
def sqrt_enclosure(x,a,b):
    a,b=F(a),F(b);assert 0<=a and a*a<=x.a and b*b>=x.b;return I(a,b)
s97=sqrt_enclosure(I(97),'9.8488578','9.8488579')
k=sqrt_enclosure(26-2*s97,'2.5104350','2.5104352')
s3=sqrt_enclosure(I(3),'1.7320508','1.7320509')
roots=[I('-1.687100','-1.687097'),I('-.109890','-.109887'),I('.442461','.442464'),I('1.354524','1.354527')]
def poly(x):return 27*x.sq().sq()-66*x.sq()+8*k*x+3
signs=[]
for x in roots:
    l,h=poly(I(x.a)),poly(I(x.b))
    assert (l.b<0<h.a) or (h.b<0<l.a)
    signs.append([l.show(),h.show()])
# Four disjoint sign-changing intervals exhaust the quartic's four roots.
t=roots[0];scores=[]
for j,x in enumerate(roots):
    co=I(1) if j==0 else (9*(1+t.sq())*(1+x.sq())-16-4*(1+3*t*x).sq())/(16*(1+3*t*x))
    assert co.a>=-1 and co.b<=1
    q=s3*x-1
    score=(4+q.sq()+4*q*co)/(12*(1+x.sq()))
    assert score.a>=0 and score.b<F(7,20) # all below .35 < .5
    scores.append(score.show())
print(json.dumps({'result':'EXPLICIT_EXAMPLE_10_2_ALPHA_LE_7_OVER_20','root_intervals':[x.show() for x in roots],'score_intervals':scores,'fixed_two_scores':'1/4','arithmetic':'exact fractions; square-root bounds verified by squaring','claim':'one witness only, not global optimum'},indent=2))
