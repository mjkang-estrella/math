#!/usr/bin/env python3
"""Independent finite interface/runner checks. Copyright 2026 Myeongjin Kang; MIT."""
from pathlib import Path
from fractions import Fraction as F
import importlib.util,json,subprocess,sys,os,hashlib
HERE=Path(__file__).resolve().parent; A=HERE.parent/'kn-minus-edge-formal-v1'
env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
results=[]
def run(label,cmd,expected):
 p=subprocess.run(cmd,cwd=HERE,env=env,capture_output=True,text=True)
 (HERE/'logs'/f'{label}.stdout').write_text(p.stdout);(HERE/'logs'/f'{label}.stderr').write_text(p.stderr)
 assert p.returncode==expected,(label,p.returncode,p.stdout,p.stderr)
 results.append({'name':label,'exit_code':p.returncode,'expected':expected,'command':list(map(str,cmd))})
run('author-payload-verify',[sys.executable,'-B',str(A/'verify.py')],0)
run('author-integer-controls',[sys.executable,'-B',str(A/'semantic_checks.py')],0)
for label,code,expected in [('runner-zero-marker','print("SOME FAIL")',1),('runner-status','print("ALL OK");raise SystemExit(7)',1),('runner-stderr','import sys;print("FAILED",file=sys.stderr)',1),('runner-success','print("ALL OK")',0)]:
 run(label,[sys.executable,'-B',str(A/'checked_run.py'),'--log-prefix',str(HERE/'logs'/f'{label}-inner'),'--',sys.executable,'-c',code],expected)
# Compute U4 matrices directly over Q, arbitrary node permutations, not using author checker.
def rank(M):
 a=[list(row) for row in M];r=0
 for j in range(len(a[0])):
  p=next((i for i in range(r,len(a)) if a[i][j]),None)
  if p is None:continue
  a[r],a[p]=a[p],a[r];v=a[r][j];a[r]=[x/v for x in a[r]]
  for i in range(len(a)):
   if i!=r:
    v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[r])]
  r+=1
 return r
matrices=[]
for s in [2,3]:
 N=2*s; nodes=[F(i*i+2*i-3) for i in range(N)]
 order=list(range(0,N,2))+list(reversed(range(1,N,2)));pos={v:i for i,v in enumerate(order)}
 weights=[1/__import__('math').prod(nodes[i]-nodes[j] for j in range(N) if i!=j) for i in range(N)]
 def pairing(l,r):
  return sum(F(1 if pos[i]<pos[j] else -1,2)*(nodes[i]-nodes[j])*weights[i]*weights[j]*l(nodes[i],nodes[j])*r(nodes[i],nodes[j]) for i in range(N) for j in range(N) if i!=j)
 L=[(a,b) for a in range(s) for b in range(s-1)]
 R=[(a,b) for a in range(s-1) for b in range(s)]
 M=[[pairing(lambda u,v,a=a,b=b:u**a*v**b,lambda u,v,c=c,d=d:u**c*v**d) for c,d in R] for a,b in L]
 assert rank(M)==s*(s-1)
 twist=[]
 for c in nodes:
  T=[[pairing(lambda u,v,a=a,b=b:u**a*v**b,lambda u,v,e=e,f=f:(v-c)*u**e*v**f) for e in range(s-1) for f in range(s-1)] for a,b in L]
  assert rank(T)==(s-1)**2
  twist.append(rank(T))
 matrices.append({'s':s,'nodes':list(map(str,nodes)),'arbitrary_label_order':order,'rectangle_rank':rank(M),'twisted_ranks_all_nodes':twist})
# Independent finite formula identities, parity and n=2..5 endpoint checks.
def z(n):return __import__('math').prod(k//2 for k in [n,n-1,n-2,n-3])//4
def deletion(n):return z(n)-__import__('math').comb((n-1)//2,2)
for n in list(range(2,120))+[10**101,10**101+1]:
 assert deletion(n)==__import__('math').prod(k//2 for k in [n+2,n-1,n-3,n-4])//4
assert [deletion(n) for n in range(2,6)]==[0,0,0,0]
results.append({'name':'independent-rational-U4-and-formulas','status':'PASS','matrices':matrices,'limitation':'finite exact rational evidence; no proof of U4 or full crossing theorem'})
(HERE/'support-checks.json').write_text(json.dumps({'status':'PASS','results':results},indent=2)+'\n')
print('PASS independent rational rectangle/twist ranks s=2,3; integer formulas; separate process marker/status/stderr controls')
