import math,random,json,time
from pathlib import Path
rng=random.Random(325507)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,s):return tuple(x*s for x in a)
def sub(a,b):return add(a,scale(b,-1))
def fun(a,f):
 t,x,z=a;r=math.hypot(x,z);u=f(t+r);v=f(t-r)
 return ((u+v)/2,x*(u-v)/(2*r) if r else 0,z*(u-v)/(2*r) if r else 0)
def dot(a,b):return 2*sum(x*y for x,y in zip(a,b))
def sq(a):return (sum(x*x for x in a),2*a[0]*a[1],2*a[0]*a[2])
def evaluate(a,b,c,q):
 d=sub(a,b);dp=fun(d,lambda t:max(t,0)**2);dn=fun(d,lambda t:min(t,0)**2)
 cp=fun(c,lambda t:max(t,0)**2);cn=fun(c,lambda t:min(t,0)**2)
 w=fun(a,math.exp);v=fun(b,math.exp)
 l=dot(c,sub(fun(a,math.exp),fun(b,math.exp)))
 u=dot(dp,w)+dot(dn,v);h=dot(cp,w)+dot(cn,v)
 return l-q*math.sqrt(max(0,u*h)), l,u,h
best=(0,None);start=time.time();count=0
for count in range(150000):
 q=1;a=tuple(rng.uniform(-2,2) for _ in range(3));b=tuple(rng.uniform(-2,2) for _ in range(3));c=tuple(rng.uniform(-2,2) for _ in range(3))
 gap,l,u,h=evaluate(a,b,c,q)
 if gap>best[0]:best=(gap,{'a':a,'b':b,'c':c,'q':q,'gap':gap,'lhs':l,'s':math.sqrt(h/u) if u else None})
 if gap>1e-4:break
out={'seed':325507,'iterations':count+1,'seconds':time.time()-start,'best':best}
Path(__file__).with_name('trace-search-exp.json').write_text(json.dumps(out,indent=2));print(out)
