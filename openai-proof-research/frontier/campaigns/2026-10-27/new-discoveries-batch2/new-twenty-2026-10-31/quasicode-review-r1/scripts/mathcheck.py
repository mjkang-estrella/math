import itertools,json,pathlib,time,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
def span(rows):
 s={0}
 for r in rows:s|={x^r for x in s}
 return s
def autos(C,n,limit=None):
 # Independently search bijections using all weight-labelled binary projection histograms.
 # At depth d require equality of joint projection counts for selected coordinates.
 weights={w:w.bit_count() for w in C};found=[];nodes=0
 def hist(coords):
  h={}
  for w in C:
   k=(weights[w],sum(((w>>c)&1)<<j for j,c in enumerate(coords)));h[k]=h.get(k,0)+1
  return h
 target=[hist(range(d)) for d in range(n+1)]
 def visit(p,unused):
  nonlocal nodes
  nodes+=1
  if len(p)==n:
   found.append(p);return limit is not None and len(found)>=limit
  for i in unused:
   q=p+(i,)
   if hist(q)==target[len(q)] and visit(q,unused-{i}):return True
  return False
 visit((),set(range(n)));return found,nodes
rows=[3833,3574,1422,2637,210,225];C=span(rows);a,nodes=autos(C,12)
r={'rows':rows,'size':len(C),'dimension':6,'words':sorted(C),'weight_distribution':[sum(w.bit_count()==k for w in C) for k in range(13)],'automorphisms':a,'backtracking_nodes':nodes,'method':'joint weight/projection histograms, no input scripts imported'}
assert len(C)==64 and a==[tuple(range(12)),tuple(i^1 for i in range(12))]
(L/'independent-12.json').write_text(json.dumps(r,indent=2)+'\n');print(r,flush=True)
