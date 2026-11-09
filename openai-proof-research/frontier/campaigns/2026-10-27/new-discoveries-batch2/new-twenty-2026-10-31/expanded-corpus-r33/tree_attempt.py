import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import networkx as nx,numpy as np,json,pathlib,resource,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
o=pathlib.Path(__file__).resolve().parent

def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 return c

def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def poly(g):
 def rec(v,p):
  a,b=[1],[0,1]
  for w in g[v]:
   if w==p:continue
   c,d=rec(w,v);a=mul(a,add(c,d));b=mul(b,c)
  return a,b
 a,b=rec(0,-1);return add(a,b)

def spider(arms):
 g=nx.Graph();g.add_node(0);v=1
 for l in arms:
  p=0
  for _ in range(l):g.add_edge(p,v);p=v;v+=1
 return g
start=time.monotonic(); best={};count=0;flags=[]
with (o/'tree-enumeration.jsonl').open('w') as f:
 for n in range(6,17):
  local=None
  for g in nx.nonisomorphic_trees(n):
   a=poly(g);r=float(max(abs(np.polynomial.polynomial.polyroots(a))));bound=2**((n-4)//2)+(n+2)//2 if n%2==0 else None
   rec={'n':n,'edges':list(g.edges()),'coefficients':a,'numeric_maxmod':r,'bound':bound,'all_ratios_bounded':all(a[i]<=bound*a[i+1] for i in range(len(a)-1)) if bound else None};f.write(json.dumps(rec)+'\n');count+=1
   if local is None or r>local['numeric_maxmod']:local=rec
   if bound and r>bound+1e-6:flags.append(rec)
  best[n]=local;print(n,local['numeric_maxmod'],'bound',local['bound'],flush=True)
# Structured arms 1,2,3,4. Exact coefficient ratio test; sign at -B is exact integer.
structured=0;ratio_fail=[];sign_flags=[]
with (o/'tree-structured.jsonl').open('w') as f:
 for a in range(9):
  for b in range(25):
   for c in range(7):
    for d in range(3):
     n=1+a+2*b+3*c+4*d
     if n<6 or n>60 or n%2:continue
     g=spider([1]*a+[2]*b+[3]*c+[4]*d);p=poly(g);B=2**((n-4)//2)+(n+2)//2
     val=0
     for x in p[::-1]:val=val*(-B)+x
     good=all(p[i]<=B*p[i+1] for i in range(len(p)-1));sgn=val*((-1)**(len(p)-1))
     rec={'arms':[a,b,c,d],'n':n,'coefficients':p,'bound':B,'all_ratios_bounded':good,'signed_value_at_minus_bound':sgn};f.write(json.dumps(rec)+'\n');structured+=1
     if not good:ratio_fail.append(rec)
     if sgn<0:sign_flags.append(rec)
out={'enumerated':count,'best_by_n':best,'numeric_flags':flags,'structured':structured,'structured_ratio_failures':ratio_fail,'exact_sign_flags':sign_flags,'wall_seconds':time.monotonic()-start,'scope':'diagnostics; numerical roots uncertified; ratio tests exact integer but no Lean semantics'}
(o/'tree-attempt-results.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',count,structured,'ratio failures',len(ratio_fail),'sign flags',len(sign_flags),flush=True)
