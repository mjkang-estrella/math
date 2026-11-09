import pathlib,json,random,itertools,sys
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(190)
vals=(-2,-1,1,2);possible=[{sum(xs) for xs in itertools.product(vals,repeat=k)} for k in range(6)]
def solve(n,es,cap=100000):
 rem=[5]*n;sums=[0]*n;un=set(range(len(es)));lab=[0]*len(es);nodes=0
 def go():
  nonlocal nodes
  nodes+=1
  if nodes>cap:return None
  if not un:return True
  best=None;opts=None
  for j in sorted(un):
   a,b=es[j];vs=[v for v in vals if -sums[a]-v in possible[rem[a]-1] and -sums[b]-v in possible[rem[b]-1]]
   if not vs:return False
   if opts is None or len(vs)<len(opts):best=j;opts=vs
   if len(vs)==1:break
  a,b=es[best];un.remove(best);rem[a]-=1;rem[b]-=1
  for v in opts:
   lab[best]=v;sums[a]+=v;sums[b]+=v;r=go();sums[a]-=v;sums[b]-=v
   if r is not False:return r
  un.add(best);rem[a]+=1;rem[b]+=1;lab[best]=0;return False
 r=go();return r,nodes,lab if r else None
out=[]
for n in range(6,25,2):
 for trial in range(20):
  es={tuple(sorted((a,(a+d)%n))) for a in range(n) for d in [1,2]};es|={tuple(sorted((a,a+n//2))) for a in range(n//2)}
  for _ in range(n*40):
   e,f=rng.sample(sorted(es),2);a,b=e;c,d=f
   if len({a,b,c,d})<4:continue
   g,h=tuple(sorted((a,c))),tuple(sorted((b,d)))
   if g not in es and h not in es:es.difference_update([e,f]);es.update([g,h])
  es=sorted(es);r,nodes,lab=solve(n,es);out.append({'n':n,'edges':es,'solved':r,'nodes':nodes,'labels':lab})
  print(n,trial,r,nodes,flush=True)
 (D/'outputs/flows.json').write_text(json.dumps(out))
print('total',len(out),'solved',sum(x['solved'] is True for x in out),'unresolved',sum(x['solved'] is None for x in out))
