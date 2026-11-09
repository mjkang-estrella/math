import pathlib,itertools,random,json
D=pathlib.Path(__file__).resolve().parents[1]
src=pathlib.Path(__file__).resolve().with_name('ci.py');ns={'__file__':str(src)}
exec(compile(src.read_text().split('rng=random.Random')[0],str(src),'exec'),ns);cost=ns['cost']
rng=random.Random(230)
def inv(a,p):
 n=len(a);a=[a[i][:]+[int(i==j) for j in range(n)] for i in range(n)]
 for j in range(n):
  q=next((i for i in range(j,n) if a[i][j]),None)
  if q is None:return
  a[j],a[q]=a[q],a[j];v=pow(a[j][j],-1,p);a[j]=[v*x%p for x in a[j]]
  for i in range(n):
   if i!=j:
    v=a[i][j];a[i]=[(x-v*y)%p for x,y in zip(a[i],a[j])]
 return [r[n:] for r in a]
out=[]
for p,n,trials in [(3,2,81),(3,3,19683)]+[(p,n,10000) for p in [3,5,101] for n in [4,6,10,16]]:
 counts={};good=0;exhaustive=(n<=3);examples=[]
 for k in range(trials):
  if exhaustive:
   vals=[]
   for _ in range(n*n):vals.append(k%p);k//=p
   a=[vals[i*n:(i+1)*n] for i in range(n)]
  else:
   density=rng.choice([.1,.2,.35,.5]);a=[[rng.randrange(1,p) if rng.random()<density else 0 for _ in range(n)] for _ in range(n)]
  b=inv(a,p)
  if b is None:continue
  good+=1;c=cost([sum(1<<j for j,x in enumerate(r) if x) for r in a],[sum(1<<j for j,x in enumerate(r) if x) for r in b],n)
  counts[c]=counts.get(c,0)+1
  if c>3 and len(examples)<3:examples.append({'A':a,'B':b,'c':c})
 row={'field':p,'n':n,'trials':trials,'invertible':good,'weakening_histogram':counts,'exhaustive_matrices':exhaustive,'c_gt_3_examples':examples};out.append(row);print(row,flush=True)
(D/'evidence/ci-fields.json').write_text(json.dumps(out,indent=2))
