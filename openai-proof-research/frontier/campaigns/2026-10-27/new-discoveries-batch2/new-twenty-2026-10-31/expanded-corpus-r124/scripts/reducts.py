import functools,itertools,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
def canon(s):
 d={};return tuple(d.setdefault(x,len(d)) for x in s)
@functools.lru_cache(None)
def reducts(w):
 children=set()
 for size in range(1,len(w)//2+1):
  for i in range(len(w)-2*size+1):
   if w[i:i+size]==w[i+size:i+2*size]:children.add(w[:i]+w[i+size:])
 if not children:return frozenset([w])
 return frozenset().union(*(reducts(v) for v in children))
seen={};out=[]
for n in range(1,13):
 count=0;vals=set()
 for w in itertools.product(range(3),repeat=n):
  if canon(w)!=w:continue
  count+=1;r=len(reducts(w));vals.add(r);seen.setdefault(r,w)
 o=dict(length=n,canonical_words=count,counts=sorted(vals),max=max(vals));out.append(o);print(o,flush=True)
(D/'outputs/reducts.json').write_text(json.dumps(dict(levels=out,witnesses=seen),indent=2))
