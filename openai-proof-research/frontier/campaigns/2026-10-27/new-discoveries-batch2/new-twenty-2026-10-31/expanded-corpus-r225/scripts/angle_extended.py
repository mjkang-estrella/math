import itertools,random,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(434225);P=1000003
def rank(a):
 a=[r[:] for r in a];r=0
 for j in range(len(a[0])):
  k=next((k for k in range(r,len(a)) if a[k][j]%P),None)
  if k is None:continue
  a[k],a[r]=a[r],a[k];iv=pow(a[r][j]%P,-1,P);a[r]=[x*iv%P for x in a[r]]
  for k in range(r+1,len(a)):
   z=a[k][j]%P
   if z:a[k]=[(x-z*y)%P for x,y in zip(a[k],a[r])]
  r+=1
  if r==len(a):return r
 return r
def matrix(n,es,cs,pos):
 c=max(cs)+1;a=[]
 for (u,v),j in zip(es,cs):
  x=pos[u][0]-pos[v][0];y=pos[u][1]-pos[v][1];r=[0]*(2*n+c);r[2*u]=x;r[2*u+1]=y;r[2*v]=-x;r[2*v+1]=-y;r[2*n+j]=-x*x-y*y;a.append(r)
 return a
def condition(n,es,cs):
 c=max(cs)+1;wanted=set(range(c));success=set();masks=[(1<<u)|(1<<v) for u,v in es]
 constraints=[(s,2*s.bit_count()-3) for s in range(1<<n) if s.bit_count()>=2]
 for remove in itertools.combinations(range(len(es)),c-1):
  cols=[cs[i] for i in remove]
  if len(set(cols))!=len(cols):continue
  missing=next(iter(wanted-set(cols)))
  if missing in success:continue
  keep=[x for i,x in enumerate(masks) if i not in remove]
  if all(sum(x&s==x for x in keep)<=b for s,b in constraints):success.add(missing)
  if len(success)==c:return True
 return False
for n in range(9,13):
 trials=eligible=full=deficient=0
 for z in range(500):
  allE=list(itertools.combinations(range(n),2));c=rng.randint(2,4);m=2*n+c-4
  if 2*c>m:continue
  es=rng.sample(allE,m);cs=list(range(c))*2+[rng.randrange(c) for _ in range(m-2*c)];rng.shuffle(cs);trials+=1
  pos=[(rng.randrange(1000),rng.randrange(1000)) for _ in range(n)]
  r=rank(matrix(n,es,cs,pos))
  if r==m:full+=1;continue
  if condition(n,es,cs):
   eligible+=1;rs=[r]
   for k in range(2):rs.append(rank(matrix(n,es,cs,[(rng.randrange(1000),rng.randrange(1000)) for _ in range(n)])))
   if max(rs)<m:
    deficient+=1;row={'n':n,'edges':es,'colors':cs,'ranks':rs,'m':m};print('POTENTIAL',json.dumps(row),flush=True)
    (D/'angle-potential.json').write_text(json.dumps(row,indent=2)+'\n');break
 print(json.dumps({'n':n,'trials':trials,'full_rank_at_first_point':full,'condition_holds_despite_first_deficiency':eligible,'persistent_deficiency':deficient}),flush=True)
 if deficient:break
