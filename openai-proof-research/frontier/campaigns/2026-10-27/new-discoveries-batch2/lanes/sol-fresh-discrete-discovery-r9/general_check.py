from spectral_probe import *

def contingencies(s,p):
 assert len(s)==len(p)==3 and sum(s)<=8
 for a in itertools.product(*(range(x+1) for x in p)):
  if sum(a)!=s[0]:continue
  rem=tuple(x-y for x,y in zip(p,a))
  for b in itertools.product(*(range(x+1) for x in rem)):
   if sum(b)!=s[1]:continue
   yield a+b+tuple(x-y for x,y in zip(rem,b))

def general_literal(alpha):
 rows=[];q=[]
 for j in range(3):
  for i in range(3):
   for _ in range(alpha[3*i+j]):
    v=i;r=0
    while True:
     if r==len(rows):rows.append([]);q.append([])
     col=next((i for i,x in enumerate(rows[r]) if x>v),len(rows[r]))
     if col==len(rows[r]):rows[r].append(v);q[r].append(j);break
     rows[r][col],v=v,rows[r][col];r+=1
 return rows,q

def general_expand(rows,q):
 out={(0,)*9:1}
 for k in range(len(rows[0])):
  rr=[r[k] for r in rows if len(r)>k];cc=[r[k] for r in q if len(r)>k]
  terms=[]
  for perm in itertools.permutations(range(len(rr))):
   v=[0]*9
   for i,j in enumerate(perm):v[3*rr[i]+cc[j]]+=1
   sign=(-1)**sum(perm[i]>perm[j] for i in range(len(perm)) for j in range(i+1,len(perm)))
   terms.append((v,sign))
  new={}
  for a,v in out.items():
   for b,w in terms:
    c=tuple(x+y for x,y in zip(a,b));new[c]=new.get(c,0)+v*w
  out={a:v for a,v in new.items() if v}
 return out

def main():
 tested=0;survivors=[];counts=[]
 for d in range(3,9):
  comps=[(a,b,d-a-b) for a in range(1,d-1) for b in range(1,d-a)]
  for s in comps:
   for p in comps:
    if s<p or max(s)+max(p)>d:continue
    ts=list(contingencies(s,p));N=len(ts);assert N<=100
    idx={x:i for i,x in enumerate(ts)};A=[[0]*N for _ in ts]
    for k,a in enumerate(ts):
     for b,v in general_expand(*general_literal(a)).items():A[idx[b]][k]=v
    tested+=1
    if plus_unipotent(A):
     import sympy as S
     t=S.Symbol('t');f=S.Poly(S.Matrix(A).charpoly(t).as_expr(),t);g=f
     for root in [1,-1]:
      while g.eval(root)==0:g=g.exquo(S.Poly(t-root,t))
     survivors.append({'s':s,'p':p,'N':N,'charpoly':str(f.as_expr().factor()),'remaining_degree':g.degree(),'matrix':A})
  counts.append({'degree':d,'cumulative_pairs':tested})
 result={'status':'PASS','coverage':counts,'mod2_survivors':survivors,'source_counterexample_found':any(x['remaining_degree']==0 for x in survivors)}
 (P/'general-checks.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k!='mod2_survivors'},indent=2));print([{k:v for k,v in x.items() if k!='matrix'} for x in survivors])
if __name__=='__main__':main()
