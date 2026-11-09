import sys,pathlib,json,hashlib
D=pathlib.Path(sys.argv[1]);p=D/sys.argv[2];s=p.read_text().strip();assert set(s)<={'+','-'};f=[0]+[1 if x=='+' else -1 for x in s];N=len(s);checks=0;worst=-10**9;arg=None
for d in range(1,N+1):
 total=0
 for a in range(2*d,N+1,d):
  total+=f[a];v=f[d]*total;assert v<=0,(d,a//d,v);checks+=1
  if v>worst:worst=v;arg=[d,a//d]
r=dict(N=N,checks=checks,verified=True,max_root_times_tail_sum=worst,max_at=arg,file=str(p.relative_to(D)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),construction='Liouville, known in source, zero novelty')
(D/'outputs'/f'divine-liouville-{N}.witness.json').write_text(json.dumps(r,indent=2));print(r)
