import os,resource
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
import mpmath as m,json
from pathlib import Path
m.mp.dps=65
def lc(x):return abs(x)+m.log1p(m.exp(-2*abs(x)))-m.log(2)
def logB(x,y,r):return (x+y)/2+lc(r*(x-y)/2)/r
def logM(x,y):
 d=abs(x-y)
 if d==0:return x
 return max(x,y)+m.log(-m.expm1(-d))-m.log(m.sqrt(2)*m.atan(d/m.sqrt(2)))
rows=[]
for sign in [-1,1]:
 q=(5+sign*m.sqrt(17))/2;p=5-2*q
 for z in [m.mpf('0.01'),m.mpf('.1'),m.mpf('.5'),1,2,4,8,16,32,64,128,256,512,1024,4096,10000]:
  u=logB(0,z,q);l=logM(0,z);r=logB(logM(0,u),logM(u,z),p)
  rows.append({'sign':sign,'z':str(z),'log_R_over_M':str(r-l)})
Path(__file__).with_name('probe-results.json').write_text(json.dumps(rows,indent=2))
print(json.dumps(rows,indent=2))
