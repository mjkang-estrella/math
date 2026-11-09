"""Single-process bounded exact integer diagnosis, NOT a theorem or Lean certificate."""
from itertools import product
from pathlib import Path
import json,time
start=time.monotonic();N=256;M=6
ps=[(3,),(0,3),(3,3),(0,0,3),(3,3,3)]
def options(d,n):
 return [(i,n-i) for i,x in enumerate(d,1) if (n>i and x&2) or (n==i and x&1)]
count=0;bad=[];maxlast=(-1,None);early=None
for o in product(range(4),repeat=4):
 ks=[i for i,x in enumerate(o,1) if x&2]
 if not ks:continue
 k=max(ks)
 oo=[options(o,n) for n in range(N+1)]
 for p in ps:
  po=[options(p,m) for m in range(M+1)];g=[[0]*(M+1) for _ in range(N+1)]
  for n in range(N+1):
   for m in range(M+1):
    vs=[i-g[r][m] for i,r in oo[n]]+[i-g[n][r] for i,r in po[m]]
    g[n][m]=max(vs) if vs else 0
  count+=1
  for m in range(M+1):
   fails=[n for n in range(N+1-2*k) if g[n+2*k][m]!=g[n][m]]
   last=max(fails,default=-1)
   if last>maxlast[0]:maxlast=(last,{'O':o,'P':p,'m':m,'k':k})
   if last>=N-64:bad.append({'O':o,'P':p,'m':m,'last':last})
   if early is None and fails:
    n=fails[0];early={'O':o,'P':p,'m':m,'n':n,'k':k,'g_n':g[n][m],'g_shift':g[n+2*k][m]}
r={'kind':'finite_diagnosis_only','O_rules_all_digits_0_to_3_length':4,'P_rules':ps,'N':N,'M':M,'rule_pairs':count,'tail_mismatches':bad,'maximum_last_mismatch':maxlast,'example_early_mismatch':early,'cpu_processes':1,'elapsed_seconds':time.monotonic()-start}
Path(__file__).with_name('scoring-probe.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
