import pathlib,json,itertools,random,sys,collections
D=pathlib.Path(__file__).resolve().parents[1]
def close(w,e):
 t=w[::-1].translate(str.maketrans('01','10')) if e else w[::-1]
 # KMP for longest suffix of w equal prefix of antimorphic reversal.
 s=t+'#'+w;pi=[0]*len(s)
 for i in range(1,len(s)):
  j=pi[i-1]
  while j and s[i]!=s[j]:j=pi[j-1]
  if s[i]==s[j]:j+=1
  pi[i]=j
 return w+t[pi[-1]:]
best=(0,None);fails=[];total=0;rng=random.Random(192)
def test(dirs):
 global total,best
 w=''
 for b,e in dirs:
  w=close(w+b,e)
  if len(w)>32768:break
 total+=1
 for n in [1,2,3,4,5,6,7,8,12,16,24,32,48,64,96,128,192,256,384,512]:
  if n*8>len(w):continue
  c=len({w[i:i+n] for i in range(len(w)-n+1)})
  if c/n>best[0]:best=(c/n,{'directive':dirs,'prefix_length':len(w),'n':n,'distinct_factors':c})
  if c>=6*n:fails.append(best[1]);print('FAIL',fails[-1],flush=True)
 return w
mode=sys.argv[1]
if mode=='exhaustive':
 for tail in itertools.product(range(4),repeat=6):test([('0',0)]+[(str(x//2),x%2) for x in tail])
else:
 for j in range(500):
  test([(str(rng.randrange(2)),rng.randrange(2)) for _ in range(18)])
  if j%25==0:print(j,best,flush=True)
z={'mode':mode,'tested':total,'best_ratio':best,'counterexamples':fails,'scope':'Distinct factors of finite closure prefixes only, hence lower bounds; no completeness claim for infinite language.'};(D/f'outputs/words-{mode}.json').write_text(json.dumps(z,indent=2));print(json.dumps(z),flush=True)
