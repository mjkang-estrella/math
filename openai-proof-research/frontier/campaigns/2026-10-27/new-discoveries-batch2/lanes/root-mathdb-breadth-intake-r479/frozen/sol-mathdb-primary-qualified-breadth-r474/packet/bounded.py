import pathlib,json,itertools,math,hashlib
O=pathlib.Path(__file__).resolve().parents[1];out=[]
# Exact public Petersen-complement certificate. Vertex labels outer0..4,inner5..9.
pedges={tuple(sorted(e)) for i in range(5) for e in [(i,(i+1)%5),(i,i+5),(i+5,5+(i+2)%5)]};E={e for e in itertools.combinations(range(10),2) if e not in pedges}
inds=[s for k in range(11) for s in itertools.combinations(range(10),k) if all(tuple(sorted(e)) not in E for e in itertools.combinations(s,2))];alpha=max(map(len,inds));maxinds=[set(s) for s in inds if len(s)==alpha];valid=[]
for k in range(11):
 for ss in itertools.combinations(range(10),k):
  s=set(ss)
  if all(s&i for i in maxinds) and all(v in s or any(tuple(sorted((v,u))) in E for u in s) for v in range(10)):valid.append(list(ss))
 if valid:break
assert alpha==2 and k==6
out.append({'mathdb_id':335848,'check':'all 1024 subsets of Petersen complement; maximum independent sets, domination and transversal conditions','alpha':alpha,'gamma_it':k,'n':10,'claimed_bound':5,'witness':valid[0],'conclusion':'public source witness replay; credit zero'})
for d in range(1,6):
 for x in [-2,0,1,2,3]:
  lhs=0
  for rho in itertools.permutations(range(1,2*d+1),d):
   prod=1
   for i,j in enumerate(rho,1):prod*=x if j<=d+1-i else (1 if j<=d+i else 0)
   lhs+=prod
  rhs=sum(math.comb(d,m)*(m+1)**d*(x-1)**(d-m) for m in range(d+1));assert lhs==rhs
out.append({'mathdb_id':335756,'check':'integer evaluations of literal generalized identity d=1..5, x=-2,0,1,2,3','result':'25 exact equalities PASS','conclusion':'bounded public identity diagnostics, not all-d proof'})
out.append({'mathdb_id':335919,'check':'x=(1,1), four sign vectors','absolute_sum':4,'mean':1,'squared_norm':2,'squared_ratio':'1/2','conclusion':'sharpness instance only; not universal lower-bound proof'})
(O/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
