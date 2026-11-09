import sys,os,random,time
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from hyper12 import twin_free,has12
rnd=random.Random(int(sys.argv[1])); secs=float(sys.argv[2]); t=time.time(); stats={}; bad=[]
while time.time()-t<secs:
    d=rnd.choice([2,3,4]); n=rnd.choice([k for k in range(6,19) if (k*d)%3==0])
    pts=[v for v in range(n) for _ in range(d)]; rnd.shuffle(pts)
    E=[tuple(sorted(pts[i:i+3])) for i in range(0,len(pts),3)]
    if any(len(set(e))<3 for e in E) or len(set(E))<len(E): continue
    tf,_=twin_free(n,E)
    if not tf: continue
    key=(n,d); stats[key]=stats.get(key,0)+1
    if not has12(n,E): bad.append(E); print('BAD',n,d,E,flush=True)
print('tested',sum(stats.values()),'by (n,d)',sorted(stats.items()),'bad',len(bad),'sec',round(time.time()-t,1))
