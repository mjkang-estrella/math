from pathlib import Path
import mpmath as mp,json,random,resource,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
mp.mp.dps=85
rng=random.Random(331384)
cases=[]
for j in range(1600):
 b=mp.mpf(rng.choice([3,4,5,8,12,30,100,1000])) if j<800 else 2+mp.power(10,rng.uniform(-3,3))
 a=mp.power(10,rng.uniform(-7,3));al=mp.power(10,rng.uniform(-6,5));be=mp.power(10,rng.uniform(-7,2));k=rng.choice([0,1,2,3,5,10,20,50,100])
 cases.append((b,a,al,be,k))
worst=None;hit=None;t0=time.time()
for j,(b,a,al,be,k) in enumerate(cases):
 def logh(t):return mp.loggamma(t+b)-mp.loggamma(t+1)-mp.loggamma(b)
 left=[logh(a+al+i)+logh(a+be+k-i) for i in range(k+1)]
 right=[logh(a+i)+logh(a+al+be+k-i) for i in range(k+1)]
 z=max(left+right);L=mp.fsum(mp.exp(t-z) for t in left);R=mp.fsum(mp.exp(t-z) for t in right);gap=(L-R)/(L+R)
 rec={'b':mp.nstr(b,35),'a':mp.nstr(a,35),'alpha':mp.nstr(al,35),'beta':mp.nstr(be,35),'k':k,'relative_gap':mp.nstr(gap,40)}
 if worst is None or gap<mp.mpf(worst['relative_gap']):worst=rec
 if gap<0:hit=rec;break
 if (j+1)%400==0:print('checked',j+1,'elapsed',round(time.time()-t0,1),flush=True)
out={'credit':0,'diagnostics_only':True,'tested':j+1,'precision_dps':mp.mp.dps,'seed':331384,'worst':worst,'hit':hit,'seconds':time.time()-t0}
(Path(__file__).parent/'screen.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
