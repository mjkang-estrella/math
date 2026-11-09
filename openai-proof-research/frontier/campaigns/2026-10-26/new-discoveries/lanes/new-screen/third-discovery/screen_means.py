import mpmath as m,json
from pathlib import Path
m.mp.dps=80
rt=m.sqrt(2)
def logdiff(x,y):
 if x<y:x,y=y,x
 return x+m.log1p(-m.exp(y-x))
def power(p,x,y):
 if p==0:return (x+y)/2
 a,b=p*x,p*y
 return (max(a,b)+m.log1p(m.exp(-abs(a-b)))-m.log(2))/p
def mean(kind,alpha,x,y):
 d=abs(y-x)
 if d<m.mpf('1e-60'):return (x+y)/2
 num=logdiff(x,y)
 if kind=='M4':return num-m.log(rt)-m.log(m.asinh(d/rt))
 if kind=='M2':return num-m.log(rt)-m.log(m.atan(d/rt))
 if kind=='L':
  if alpha==0:return num-m.log(d)
  return m.log(2*alpha)+alpha*(x+y)+num-logdiff(2*alpha*x,2*alpha*y)
 if kind=='S':return m.log(alpha)+num-m.log(2*m.atan(m.tanh(alpha*d/2)))
xs=[m.mpf(j)/10 for j in range(1,31)]+[m.mpf(j) for j in range(4,101)]+[m.mpf(200),m.mpf(500),m.mpf(1000)]
configs=[]
for kind,D,c,sgn in [('M4',21,3,1),('M2',17,5,-1)]:
 for e in [-1,1]:
  q=(c+e*m.sqrt(D))/2;p=c-2*q;configs.append((kind,m.mpf(0),p,q,sgn))
for a in [m.mpf(j)/100 for j in range(1,50)]:
 for e in [-1,1]:
  p=e*m.sqrt(1+16*a*a-16*a**4);q=(1-p)/2-2*a*a;configs.append(('L',a,p,q,-1))
for a in [m.sqrt(2-m.sqrt(3))/2,m.sqrt(2+m.sqrt(3))/2]:
 for e in [-1,1]:
  p=e*m.sqrt((1-12*a*a+112*a**4-64*a**6)/(1+4*a*a));q=(1-p)/2+2*a*a;configs.append(('S',a,p,q,-1))
for kind,a,p,q,sgn in configs:
 for x in xs:
  z=power(q,-x,x);u=mean(kind,a,-x,z);v=mean(kind,a,z,x)
  diff=mean(kind,a,-x,x)-power(p,u,v)
  if diff*sgn < -m.mpf('1e-40'):
   o={'kind':kind,'alpha':str(a),'p':str(p),'q':str(q),'x':str(x),'logdiff':str(diff)}
   Path('third-discovery/means-hit.json').write_text(json.dumps(o,indent=2));print(o,flush=True);break
 else:continue
 break
else:print('No strict sign failure across',len(configs),'configurations and',len(xs),'x values',flush=True)
