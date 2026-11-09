import pathlib,json,random,itertools,sys,math,time
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(159);out=[]
mode=sys.argv[1]
if mode=='generate':
 with (D/'outputs/orientation-random.txt').open('w') as f:
  for n in [8,9]:
   for trial in range(40):
    es={(rng.randrange(v),v) for v in range(1,n)}
    opts=list(set(itertools.combinations(range(n),2))-es);rng.shuffle(opts)
    es.update(opts[:rng.randrange(2,7)]);es=sorted(es)
    f.write(str(n)+' '+str(len(es))+' '+' '.join(str(x) for e in es for x in e)+'\n')
 print('80 seeded connected graphs orders 8 and 9')
else:
 for n in range(8,14):
  for trial in range(40):
   p=[.15,.25,.4,.6,.8][trial%5]
   es=[(a,b) for a,b in itertools.combinations(range(n),2) if rng.random()<p]
   adj=[0]*n
   for a,b in es:adj[a]|=1<<b;adj[b]|=1<<a
   # Longest cycle through each vertex subset by exact subset DP.
   gam=[0]*(1<<n)
   for r in range(n):
    dp={1<<r:1<<r}
    for s in range(1<<r,1<<n):
     ends=dp.get(s,0)
     if not ends:continue
     if s.bit_count()>=3 and ends&adj[r]:gam[s]=s.bit_count()
     while ends:
      v=(ends&-ends).bit_length()-1;ends&=ends-1
      new=adj[v]&~s&~((1<<(r+1))-1)
      while new:
       bit=new&-new;new-=bit
       dp[s|bit]=dp.get(s|bit,0)|bit
   for v in range(n):
    for s in range(1<<n):
     if not s>>v&1:gam[s]=max(gam[s],gam[s|1<<v])
   vals={}
   for t in range(3,min(n,6)+1):
    val=Fraction(0)
    for comb in itertools.combinations(range(n),t):
     s=sum(1<<x for x in comb)
     if all(adj[v]&s==s^(1<<v) for v in comb):val+=Fraction(math.comb(gam[s],2),math.comb(gam[s],t))
    vals[t]=str(val)
    if val>len(es):print('COUNTEREXAMPLE',n,es,t,val,flush=True)
   out.append({'n':n,'trial':trial,'p':p,'edges':es,'sums':vals})
  (D/'outputs/cycle-random.json').write_text(json.dumps(out))
  print('completed n',n,'total',len(out),flush=True)
