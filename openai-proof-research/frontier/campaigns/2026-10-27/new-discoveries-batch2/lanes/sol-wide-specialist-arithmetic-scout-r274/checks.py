import itertools,math,heapq,json,pathlib
L=pathlib.Path(__file__).resolve().parent
def apery(g):
 m=g[0];d=[10**12]*m;d[0]=0;h=[(0,0)]
 while h:
  v,r=heapq.heappop(h)
  if v!=d[r]:continue
  for a in g[1:]:
   s=(r+a)%m;w=v+a
   if w<d[s]:d[s]=w;heapq.heappush(h,(w,s))
 return d
def info(g):
 a=apery(g);m=g[0]
 def mem(x):return x>=0 and x>=a[x%m]
 if any(mem_from(g[:i]+g[i+1:],x) for i,x in enumerate(g)):return None
 pf=[w-m for w in a if all(mem(w-m+x) for x in g)]
 f=max(a)-m; cr=all(mem(m+f-p) for p in pf)
 ng={x:[p for p in pf if all(mem(x+p-q) for q in pf)] for x in g}
 return {'g':g,'apery':a,'PF':pf,'F':f,'type':len(pf),'canonical':cr,'NG_choices':ng}
def mem_from(g,x):
 hit=[False]*(x+1);hit[0]=True
 for n in range(1,x+1):hit[n]=any(n>=a and hit[n-a] for a in g)
 return hit[x]
if __name__=='__main__':
 count=canon=0;bytype={};examples={};largest=None;noncanonical=None
 for g in itertools.combinations(range(4,43),4):
  if math.gcd(*g)!=1:continue
  d=info(g)
  if d is None:continue
  count+=1
  if not d['canonical'] and d['type']>=5 and noncanonical is None:noncanonical=d
  if d['canonical']:
   canon+=1;t=d['type'];bytype[t]=bytype.get(t,0)+1;examples.setdefault(t,d)
   if largest is None or t>largest['type']:largest=d
 witnesses=[info((16,17,19,39)),info((5,6,7,8)),info((6,7,8,9,10,11)),noncanonical]
 # Independent membership checks on both sides of the conductor for every retained witness.
 for d in witnesses+list(examples.values()):
  a=d['apery'];g=d['g'];m=g[0]
  for x in range(0,2*max(a)+1): assert mem_from(g,x)==(x>=a[x%m])
  assert all(not mem_from(g,p) and all(mem_from(g,p+x) for x in g) for p in d['PF'])
  maxima=[p+m for p in d['PF']];W=max(a)
  reflect=all(W+m-w in a for w in maxima if w!=W)
  assert reflect==d['canonical']
  d['boundary_reflections']={w:W+m-w for w in maxima if w!=W}
 result={'scope':'all minimally 4-generated semigroups with all generators in [4,42]; no universal inference','tested':count,'canonical':canon,'types':bytype,'examples':examples,'largest':largest,'witnesses':witnesses}
 (L/'exact-checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
