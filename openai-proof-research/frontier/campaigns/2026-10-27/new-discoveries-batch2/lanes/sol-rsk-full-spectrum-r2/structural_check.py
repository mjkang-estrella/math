from check import *

def insert(alpha):
 m=len(alpha);n=len(alpha[0]);assert m<=4 and n<=4 and sum(map(sum,alpha))<=20
 rows=[];q=[]
 for j in range(n):
  for i in range(m):
   for _ in range(alpha[i][j]):
    v=i;r=0
    while True:
     if r==len(rows):rows.append([]);q.append([])
     c=next((c for c,w in enumerate(rows[r]) if w>v),len(rows[r]))
     if c==len(rows[r]):rows[r].append(v);q[r].append(j);break
     rows[r][c],v=v,rows[r][c];r+=1
 return rows,q

def poly(alpha):
 m=len(alpha);n=len(alpha[0]);rows,q=insert(alpha);out={(0,)*(m*n):1};ops=0
 for c in range(len(rows[0])):
  rr=[r[c] for r in rows if len(r)>c];cc=[r[c] for r in q if len(r)>c];terms=[]
  for perm in itertools.permutations(range(len(rr))):
   b=[0]*(m*n)
   for i,j in enumerate(perm):b[rr[i]*n+cc[j]]+=1
   terms.append((b,(-1)**sum(perm[i]>perm[j] for i in range(len(perm)) for j in range(i+1,len(perm)))))
  nxt={}
  for a,v in out.items():
   for b,w in terms:
    ops+=1;assert ops<=1000000
    z=tuple(x+y for x,y in zip(a,b));nxt[z]=nxt.get(z,0)+v*w
  out={a:v for a,v in nxt.items() if v};assert len(out)<=10000
 return out

def dilation(t,k):return [[x for x in row for _ in range(k)] for row in t]
def mod2(f):return {a:v%2 for a,v in f.items() if v%2}
def main():
 cases=[[[0,1,1],[1,1,0]],[[0,1,0],[0,0,1],[1,0,0]],[[1,1,0],[0,1,1],[1,0,1]],[[0,1,0,0],[0,0,1,0],[0,0,0,1],[1,0,0,0]]]
 checks=[]
 for alpha in cases:
  double=[[2*x for x in row] for row in alpha]
  r,q=insert(alpha);rr,qq=insert(double)
  assert rr==dilation(r,2) and qq==dilation(q,2)
  f=poly(alpha);lhs=mod2(poly(double));rhs={tuple(2*x for x in a):v for a,v in mod2(f).items()}
  assert lhs==rhs
  checks.append({'alpha':alpha,'dilation_tableaux':'PASS','Frobenius_commutation':'PASS'})
 alpha=cases[0];double=[[2*x for x in row] for row in alpha];double[0][0]+=1
 lhs=mod2(poly(double));rhs={tuple(2*x+(i==0) for i,x in enumerate(a)):v for a,v in mod2(poly(alpha)).items()}
 diff={a:1 for a in set(lhs)^set(rhs)};assert diff
 out={'status':'PASS','all_dimension_lemma_diagnostics':checks,'residue_factorization_obstruction':{'alpha':alpha,'residue_variable':'z11','output_exponents_row_major':list(diff),'coefficient_field':'F2','formula':'T(z11*f^2) + z11*T(f)^2'}}
 (P/'structural-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
