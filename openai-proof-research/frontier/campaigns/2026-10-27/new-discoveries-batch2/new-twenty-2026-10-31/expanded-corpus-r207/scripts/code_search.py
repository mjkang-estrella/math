from pathlib import Path
import json,random,itertools,time,math
L=Path(__file__).resolve().parents[1];random.seed(207);F=json.loads((L/'outputs/codes-factors-109.json').read_text())['nontrivial_irreducible_factors_ascending_coefficients']
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%3
 return c
start=time.monotonic();out=[]
for i,j in itertools.combinations(range(4),2):
 g=mul([2,1],mul(F[i],F[j])); rev=[x*pow(g[0],-1,3)%3 for x in reversed(g)]
 if g!=rev:continue
 rows=[[0]*k+g+[0]*(53-k) for k in range(54)]
 # exact Gaussian elimination to systematic form, no column permutation needed
 for k in range(54):
  z=pow(rows[k][k],-1,3);rows[k]=[v*z%3 for v in rows[k]]
  for r in range(54):
   if r!=k and rows[r][k]:
    z=rows[r][k];rows[r]=[(a-z*b)%3 for a,b in zip(rows[r],rows[k])]
 best=109;steps=0;restarts=0;bestword=None
 while time.monotonic()-start<100 and restarts<100:
  restarts+=1;v=[random.randrange(3) for _ in range(54)];word=[sum(v[k]*rows[k][t] for k in range(54))%3 for t in range(109)];cost=word.count(0)
  for step in range(2000):
   k=random.randrange(54);z=random.choice([1,2]);new=[(a+z*b)%3 for a,b in zip(word,rows[k])];nc=new.count(0);temperature=.3+1.2*(1-step/2000)
   if nc<=cost or random.random()<math.exp((cost-nc)/temperature):word=new;cost=nc;v[k]=(v[k]+z)%3
   steps+=1
   if cost<best:best=cost;bestword=word[:];print('IMPROVE',i,j,best,steps,flush=True)
   if cost==0:break
  if best==0:break
 out.append({'factor_indices': [i,j],'generator':g,'best_zero_count':best,'best_word':bestword,'moves':steps,'restarts':restarts})
 if time.monotonic()-start>=100:break
(L/'outputs/code-search-109.json').write_text(json.dumps(out,indent=2));print('DONE',[(x['factor_indices'],x['best_zero_count']) for x in out],flush=True)
