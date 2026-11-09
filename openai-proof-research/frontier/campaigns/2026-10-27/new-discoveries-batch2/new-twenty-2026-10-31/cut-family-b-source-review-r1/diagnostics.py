import resource,os,time,json,pathlib
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(70,70));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);start=time.monotonic()
def formula(c,n):
 q,r=divmod(n-1,12*c); block,t=divmod(r,2*c)
 low=([0,1][t%2] if block==0 else [2,3][t%2] if block==1 else (1 if t==0 else [5,4][t%2]) if block==2 else [3,2][t%2] if block==3 else [4,5][t%2] if block==4 else [6,7][t%2])
 return 8*q+low
def W(c,v): return 12*c*(v//8)+(4*c+1)*((v>>2)&1)+2*c*((v>>1)&1)+(v&1)
def game(c,extended,N):
 g=[0]*(N+1); dp=[[set() for _ in range(N+1)] for _ in range(N+1)];dp[0][0]={0}
 for n in range(1,N+1):
  opts=set()
  for k in range(2,n+1):
   vals=dp[k][n]
   for h in range(1,n-k+2): vals.update(g[h]^v for v in dp[k-1][n-h])
   d=k-1
   if d in (1,2*c) or (extended and ((d%2==0 and d>=2*c) or (d%2==1 and d>6*c))):opts.update(vals)
  v=0
  while v in opts:v+=1
  g[n]=v;dp[1][n]={v}
  assert v==formula(c,n),(c,extended,n,v,formula(c,n))
 return {'c':c,'extended_maximal_cuts_below_N':extended,'N':N,'values':g[1:]}
rows=[game(c,e,80) for c in [2,3,4,7] for e in [False,True]]
for c in [2,3,4,7,31,100]:
 for n in list(range(1,36*c+1))+[12*c*(2**100+2**51+7)+r for r in [1,4*c+1,4*c+2,8*c,12*c]]:assert 1<=n-W(c,formula(c,n))<=6*c
 for a in list(range(128))+[2**100-1,2**100,2**100+7]:
  for b in list(range(128))+[2**100-1,2**100,2**100+7]: assert W(c,a^b)<=W(c,a)+W(c,b)
o={'scope':'finite diagnostics only; DP uses actual mex and ordered positive compositions, not assumed formula','caps':{'cpus':2,'memory_MiB':768,'cpu_seconds':70,'wall_seconds':85},'seconds':time.monotonic()-start,'games':rows,'assertions':'all passed'};p=pathlib.Path(__file__).resolve().parent;(p/'diagnostics.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o,indent=2))
