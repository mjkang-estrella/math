# Batch driver for 378740 pool screens: seeded line-arrangement pools, all N-subsets per pool via bin/dbl2.
# Args: batch_name K box seed_lo seed_hi extra maxpool deadline_seconds
import sys,subprocess,json,time,pathlib,re,math
D=pathlib.Path(__file__).resolve().parents[1]; sys.path.insert(0,str(D/'scripts')); from pools import pool
REF={(5,2):'1,2,3,4,5,6,6,5,2,2',(5,3):'1,2,3,4,5,6,6,6,3,3',(5,4):'1,2,3,4,5,6,6,6,5,4',
     (6,1):'1,2,3,4,5,6,7,6,6,6,1,1',(6,2):'1,2,3,4,5,6,7,7,6,6,2,2',(6,3):'1,2,3,4,5,6,7,7,7,6,3,3',
     (6,4):'1,2,3,4,5,6,7,7,7,7,4,4',(6,5):'1,2,3,4,5,6,7,7,7,7,6,5'}
name,K,box,lo,hi,extra,maxpool,deadline=sys.argv[1],*map(int,sys.argv[2:9])
t0=time.monotonic(); out=[]; cands=[]
for seed in range(lo,hi):
  lines,pts=pool(K,box,seed,extra)
  f=D/f'tmp/pools/{name}-{seed}.txt'; f.write_text(''.join(f'{x} {y} {z}\n' for x,y,z in pts))
  for (t,r),ref in REF.items():
    N=t*(t-1)//2+r
    if len(pts)<N or len(pts)>maxpool or math.comb(len(pts),N)>60000: continue
    if time.monotonic()-t0>deadline: break
    o=subprocess.run([str(D/'bin/dbl2'),str(t),str(r),ref,str(f)],capture_output=True,text=True).stdout
    m=re.search(r'subsets=(\d+) generic=(\d+) candidates=(\d+)',o)
    rec=dict(seed=seed,K=K,box=box,extra=extra,lines=lines,pool=len(pts),t=t,r=r,subsets=int(m[1]),generic=int(m[2]),candidates=int(m[3]))
    out.append(rec)
    if rec['candidates']: cands.append(dict(rec,output=o)); print('CANDIDATE',rec,flush=True)
  if time.monotonic()-t0>deadline: break
s=dict(batch=name,completed_seeds=sorted({r['seed'] for r in out}),runs=len(out),subsets=sum(r['subsets'] for r in out),generic=sum(r['generic'] for r in out),candidates=cands,records=out)
(D/f'outputs/dbl-{name}.json').write_text(json.dumps(s,indent=1)+'\n'); print({k:v for k,v in s.items() if k!='records'})
