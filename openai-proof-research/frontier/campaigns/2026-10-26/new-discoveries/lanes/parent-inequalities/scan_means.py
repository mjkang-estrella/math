import mpmath as m, json
from pathlib import Path
m.mp.dps=100
def power(a,b,p):
 if p==0:return m.sqrt(a*b)
 return m.exp(m.log((m.exp(p*m.log(a))+m.exp(p*m.log(b)))/2)/p)
def meanL(a,b,alpha):
 if a==b:return a
 if alpha==0:return (b-a)/m.log(b/a)
 return 2*alpha*(a*b)**alpha*(b-a)/(b**(2*alpha)-a**(2*alpha))
def meanS(a,b,alpha):
 if a==b:return a
 return alpha*(b-a)/(2*m.atan((b**alpha-a**alpha)/(b**alpha+a**alpha)))
def meanM4(a,b):
 if a==b:return a
 return (b-a)/(m.sqrt(2)*m.asinh(m.log(b/a)/m.sqrt(2)))
def diff(M,t,p,q):
 a=m.mpf(1);b=m.exp(t);N=power(a,b,q)
 R=power(M(a,N),M(N,b),p)
 return (M(a,b)-R)/M(a,b)
rows=[]
ts=[m.mpf(v) for v in ['.001','.01','.05','.1','.5','1','2','4','8','16','32','64','128','256','512','1024','2048']]
for fam in ['L','S','M4']:
 alphas=([m.mpf(v) for v in ['.001','.01','.05','.1','.15','.2','.25','.3','.35','.4','.45','.49','.499']] if fam=='L' else [m.sqrt(2-m.sqrt(3))/2,m.sqrt(2+m.sqrt(3))/2] if fam=='S' else [None])
 for alpha in alphas:
  for branch in [-1,1]:
   if fam=='L':p=branch*m.sqrt(1+16*alpha**2-16*alpha**4);q=(1-p)/2-2*alpha**2;M=lambda a,b:meanL(a,b,alpha);sign=-1
   elif fam=='S':p=branch*m.sqrt((1-12*alpha**2+112*alpha**4-64*alpha**6)/(1+4*alpha**2));q=(1-p)/2+2*alpha**2;M=lambda a,b:meanS(a,b,alpha);sign=-1
   else:q=(3+branch*m.sqrt(21))/2;p=3-2*q;M=meanM4;sign=1
   worst=None
   for t in ts:
    d=diff(M,t,p,q);score=sign*d
    if worst is None or score<worst[0]:worst=(score,t,d)
   r={'family':fam,'alpha':None if alpha is None else str(alpha),'branch':branch,'p':str(p),'q':str(q),'worst_signed_relative_gap':str(worst[0]),'log_ratio':str(worst[1]),'difference':str(worst[2]),'violation':bool(worst[0]<-m.mpf('1e-60'))}
   rows.append(r)
   if r['violation']:print(json.dumps(r),flush=True)
Path(__file__).with_name('means-scan.json').write_text(json.dumps({'status':'numerical_experiment_only','dps':m.mp.dps,'rows':rows},indent=2))
print('scanned',len(rows),'parameterbranches; violations',sum(r['violation'] for r in rows))
