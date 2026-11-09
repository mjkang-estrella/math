import pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1]
checks=[]
for n in [11,12,13]:
 o=json.loads((D/f'outputs/pinnacle{n}.json').read_text());c=o['counts'];assert all(isinstance(z,int) for z in c);assert sum(c)==math.factorial(n);sets=0;bad=[]
 for s in range(1<<n):
  v=c[s*(n+2):(s+1)*(n+2)]
  if not any(v):continue
  sets+=1;assert v==v[::-1]
  for j in range((n+1)//2+1):
   g=v[j]
   if g<0:bad.append([s,j,g])
   for k in range(n+2-2*j):v[j+k]-=g*math.comb(n+1-2*j,k)
  assert not any(v)
 assert not bad;checks.append({'n':n,'exact_integer_sum':sum(c),'nonempty_pinnacle_sets':sets,'negative_gamma':bad})
print(checks);(D/'outputs/validation.json').write_text(json.dumps(checks,indent=2))
r=json.loads((D/'outputs/registry-screen.json').read_text())
for k,v in r.get('keyword_path_matches',{}).items():
 if v:print('REGISTRY',k,len(v),str(v)[:450])
