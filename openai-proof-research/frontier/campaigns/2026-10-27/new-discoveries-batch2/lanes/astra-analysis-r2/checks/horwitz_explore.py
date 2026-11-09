"""Numerical exploration only; not proof."""
import mpmath as m, json, random
from pathlib import Path
m.mp.dps=80

def L(a,b):
 if a==b:return a
 return (b-a)/m.log(b/a)
def U(a,b,c):
 a,b,c=sorted([a,b,c])
 if a==b or b==c:return None
 num=(b-c)*(a-c)*(a-b)/2
 d0=a*m.log(b/c)+c*m.log(a/b)+b*m.log(c/a)
 d1=a*(b-c)*m.log(a)-b*(a-c)*m.log(b)+c*(a-b)*m.log(c)
 return m.sqrt(num/d0),num/d1
def T(v):
 a,b,c=v;return (L(a,b),L(b,c),L(a,c))
def run():
 out=[];random.seed(376978)
 for i in range(500):
  x=m.mpf(random.uniform(-15,15)); y=m.mpf(random.uniform(-15,15))
  v=tuple(map(m.exp,[x,y,0]));u=U(*v);tu=U(*T(v));w=v
  for j in range(12):w=T(w)
  signs=(tu[0]>=u[0],tu[1]<=u[1],u[0]<=min(w),max(w)<=u[1])
  if not all(signs):out.append(dict(x=str(x),y=str(y),ratios=[str(tu[k]/u[k]) for k in [0,1]],signs=signs))
 Path(__file__).with_name('horwitz-explore.json').write_text(json.dumps(dict(samples=500,precision=80,failures=out),indent=2))
 print('failures',len(out));print(out[:3])
if __name__=='__main__':run()
