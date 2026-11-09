import random,itertools,time,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];rng=random.Random(115);start=time.monotonic();stats={'sampled':0,'general_position_hull6':0,'pairings_tested':0,'decomposable':0,'necessary_staircase_condition_passed':0}
def det(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def hull(P):
 out=[]
 for order in [sorted(range(10),key=P.__getitem__),sorted(range(10),key=P.__getitem__,reverse=True)]:
  h=[]
  for v in order:
   while len(h)>1 and det(P[h[-2]],P[h[-1]],P[v])<=0:h.pop()
   h.append(v)
  out+=h[:-1]
 return out
def pairings(v):
 if not v:yield [];return
 for j in range(1,len(v)):
  for p in pairings(v[1:j]+v[j+1:]):yield [(v[0],v[j])]+p
def solve(P,pairs):
 def cross(e,f):
  a,b=e;c,d=f
  return len({a,b,c,d})==4 and det(P[a],P[b],P[c])*det(P[a],P[b],P[d])<0 and det(P[c],P[d],P[a])*det(P[c],P[d],P[b])<0
 if any(cross(e,f) for e,f in itertools.combinations(pairs,2)):return None
 vs=list(itertools.combinations(range(5),2));forests=[[] for _ in range(5)];adj=[[] for _ in range(20)]
 for v,(i,j) in enumerate(vs):
  a,b=pairs[i];c,d=pairs[j]
  for bit in range(2):
   first=[(a,c),(b,d)] if bit==0 else [(a,d),(b,c)];second=[(a,d),(b,c)] if bit==0 else [(a,c),(b,d)]
   forests[i].append((v,bit,first));forests[j].append((v,bit,second))
 for f in forests:
  for v,b,es in f:
   if cross(es[0],es[1]):adj[2*v+b].append(2*v+1-b)
  for (v,b,es),(w,c,fs) in itertools.combinations(f,2):
   if v!=w and any(cross(e,z) for e in es for z in fs):adj[2*v+b].append(2*w+1-c);adj[2*w+c].append(2*v+1-b)
 # full transitive reachability, only 20 literals
 reach=[]
 for i in range(20):
  seen={i};stack=[i]
  while stack:
   for j in adj[stack.pop()]:
    if j not in seen:seen.add(j);stack.append(j)
  reach.append(seen)
 if any(2*v+1 in reach[2*v] and 2*v in reach[2*v+1] for v in range(10)):return None
 for bits in itertools.product(range(2),repeat=10):
  if all(bits[j//2]==j%2 for v,b in enumerate(bits) for j in adj[2*v+b]):return {'pairs':pairs,'bits':bits}
 return None
def necessary(P,H):
 inner=[i for i in range(10) if i not in H]
 for hh in [H,H[::-1]]:
  for t in range(6):
   h=hh[t:]+hh[:t];aa=h[:-1];b1=h[-1]
   for perm in itertools.permutations(inner):
    bb=(b1,)+perm;okay=True
    for i in range(2,5):
     for l in range(i):
      for j in range(l+1,i):
       signs=[det(P[a],P[b],P[bb[i]]) for a,b in [(aa[l],bb[l]),(bb[l],aa[j]),(aa[j],aa[l])]]
       if not(all(s>0 for s in signs) or all(s<0 for s in signs)):okay=False;break
      if not okay:break
     if not okay:break
    if okay:return True
 return False
while time.monotonic()-start<110:
 stats['sampled']+=1;P=rng.sample(list(itertools.product(range(20),repeat=2)),10)
 if any(det(*(P[i] for i in t))==0 for t in itertools.combinations(range(10),3)):continue
 H=hull(P)
 if len(H)!=6:continue
 stats['general_position_hull6']+=1
 # first test necessary condition; search all pairings only for potential non-staircases
 if necessary(P,H):stats['necessary_staircase_condition_passed']+=1;continue
 for pairs in pairings(list(range(10))):
  stats['pairings_tested']+=1;w=solve(P,pairs)
  if w:
   stats['decomposable']+=1;(D/'outputs/staircase-candidate.json').write_text(json.dumps(dict(points=P,hull=H,witness=w),indent=2));print('CANDIDATE',flush=True);break
 if stats['decomposable']:break
(D/'outputs/stairs.json').write_text(json.dumps(stats,indent=2)+'\n');print(stats,flush=True)
