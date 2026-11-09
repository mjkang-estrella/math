import itertools,functools,json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
# Distinct literal game trees through birthday 3, encoded as frozensets of options.
games=[frozenset()]
for rank in range(3):
 prev=list(games)
 games=list(dict.fromkeys(games+[frozenset(s) for j in range(len(prev)+1) for s in itertools.combinations(prev,j)]))
zero=frozenset();star=frozenset([zero])
@functools.lru_cache(None)
def outcome(position,misere):
 # Literal disjunctive sum, keeping duplicate components.
 opts=[]
 for i,g in enumerate(position):
  for h in g:
   q=list(position);q[i]=h;q=tuple(sorted((x for x in q if x),key=repr));opts.append(q)
 if not opts:return misere
 return any(not outcome(q,misere) for q in opts)
def canonical(gs):return tuple(sorted((x for x in gs if x),key=repr))
res=[]
for gi,g in enumerate(games):
 closed={g,star,zero};todo=list(closed)
 for a in todo:
  for b in a:
   if b not in closed:closed.add(b);todo.append(b)
 gens=sorted(closed-{zero,star},key=repr);ng=len(gens)
 samples=[];evil=True
 for length in range(7):
  for inds in itertools.combinations_with_replacement(range(ng+1),length):
   pos=canonical([star if i==ng else gens[i] for i in inds]);ps=canonical(list(pos)+[star])
   a,b=outcome(pos,False),outcome(pos,True);c,d=outcome(ps,False),outcome(ps,True)
   kin=a==b;kout=a==d and b==c
   if not kin and not kout:evil=False
   samples.append((inds,kin,kout))
 possible=[]
 for bits in range(1<<ng):
  if all((kin if any(i<ng and bits>>i&1 for i in inds) else kout) for inds,kin,kout in samples):possible.append(bits)
 print('COMPLETE',gi,'components',ng+1,'sum_states',len(samples),'truncated_evil',evil,'normal_choices',possible,flush=True)
 res.append({'game_index':gi,'literal_game':repr(g),'components':ng+1,'sum_states':len(samples),'truncated_evil':evil,'normal_choices':possible})
(D/'outputs/evil.json').write_text(json.dumps(res,indent=2))
