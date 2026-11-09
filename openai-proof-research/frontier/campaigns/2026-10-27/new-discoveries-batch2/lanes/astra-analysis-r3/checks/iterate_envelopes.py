import mpmath as m,json
from pathlib import Path
m.mp.dps=100

def L(a,b):return a if a==b else (b-a)/(m.log(b)-m.log(a))
def T(v):a,b,c=v;return L(a,b),L(a,c),L(b,c)
def means(v):return m.root(m.fprod(v),3),sum(v)/3,(sum(m.root(x,3) for x in v)/3)**3
ps=[m.mpf(10)**k for k in range(-6,4)] + [m.mpf(2),m.mpf(3),m.mpf(30),m.mpf(300)]
fails={k:[] for k in ['G1','G2','A1','A2','P13T']}
for p in ps:
 for q in ps:
  a,b,c=m.exp(-p),m.mpf(1),m.exp(q);v=(a,b,c)
  x,z=-m.expm1(-p)/p,m.expm1(q)/q;y=(p*x+q*z)/(p+q);d=z-x
  s0=d/(x*y*z*(p+q));s1=1/y-s0;u0=m.sqrt(1/(2*s0));u1=1/(2*s1)
  g1,a1,pt=means(T(v));g2,a2,_=means(T(T(v)))
  for k,w in [('G1',g1/u0),('G2',g2/u0),('A1',u1/a1),('A2',u1/a2),('P13T',u1/pt)]:
   if w<1:fails[k].append(dict(p=str(p),q=str(q),ratio=str(w)))
print({k:len(v) for k,v in fails.items()})
for k,v in fails.items(): print(k,v[:3])
Path(__file__).with_suffix('.json').write_text(json.dumps(dict(label='Exploration only',failures=fails),indent=2))
