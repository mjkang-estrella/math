from pathlib import Path
from functools import cache
import itertools,json,resource,os
R=Path(__file__).resolve().parent
os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,)*2)
V=frozenset(range(7));edges=[(0,1),(0,5),(1,2),(1,6),(2,3),(3,4),(4,5),(5,6)]
N=tuple(frozenset({v}|{w for x,y in edges for w in ([y] if x==v else [x] if y==v else [])}) for v in V)
def owns(s):return any(t<=s for t in N)
def dominates(d):return all(t&d for t in N)
# Actual three-set game with both terminal conditions and total further S-move minimax cost.
@cache
def value(s,d,turn):
 assert s.isdisjoint(d)
 if owns(s):return 0
 if dominates(d):return float('inf')
 a=V-s-d
 assert a # a full board must have a winner
 vals=[value(s|{v},d,False)+1 if turn else value(s,d|{v},True) for v in a]
 return min(vals) if turn else max(vals)
@cache
def budget(s,a,turn,b):
 if owns(s):return True
 if turn:return b>0 and any(budget(s|{v},a-{v},False,b-1) for v in a)
 return bool(a) and all(budget(s,a-{v},True,b) for v in a)
comparisons=0
for assign in itertools.product(range(3),repeat=7):
 s=frozenset(v for v in V if assign[v]==1);d=frozenset(v for v in V if assign[v]==2);a=V-s-d
 for turn in [True,False]:
  for b in range(6):
   assert budget(s,a,turn,b)==(value(s,d,turn)<=b);comparisons+=1
assert value(frozenset(),frozenset(),True)==4
# Read the revised lower table, independently check each proposed response and every third S move.
t=(R.parent/'staller-parent-revision-r1/proof.md').read_text(); positions=thirds=0
for l in t.splitlines():
 if not l.startswith('|') or not l[1:2].isdigit():continue
 s1,d1,m=l.strip('|').split('|');s1,d1=int(s1),int(d1);assert s1!=d1
 for item in m.split(','):
  s2,d2=map(int,item.split(':'));assert len({s1,d1,s2,d2})==4;positions+=1
  for s3 in V-{s1,d1,s2,d2}:
   assert not owns(frozenset([s1,s2,s3]));thirds+=1
out={'closed_neighborhoods':[sorted(t) for t in N],'degrees':[len(t)-1 for t in N],'S_start_number':value(frozenset(),frozenset(),True),'D_start_number':str(value(frozenset(),frozenset(),False)),'all_partition_turn_budget_comparisons':comparisons,'lower_table_positions':positions,'third_move_checks':thirds,'S_first_move_values':{str(v):str(value(frozenset([v]),frozenset(),False)+1) for v in V},'value_states':value.cache_info()._asdict()}
(R/'independent-game.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))

# Independently validate the author's upper strategy tree, not its verifier.
tree=json.loads((R.parent/'expanded-corpus-r48/strategy.log').read_text().split('\n',1)[1])
nodes=leaves=0;max_cost=0
def verify(t,s,d,turn,c):
 global nodes,leaves,max_cost
 nodes+=1
 if 'win' in t:
  target=frozenset(v for v in V if t['win']&(1<<v))
  assert owns(target) and target<=s and c<=4 and not dominates(d)
  leaves+=1;max_cost=max(max_cost,c);return
 assert not owns(s) and not dominates(d)
 a=V-s-d
 if turn:
  v=t['S'];assert v in a;verify(t['next'],s|{v},d,False,c+1)
 else:
  assert set(map(int,t['D']))==a
  for v,child in t['D'].items():verify(child,s,d|{int(v)},True,c)
verify(tree,frozenset(),frozenset(),True,0)
print('Upper tree:',nodes,'nodes',leaves,'leaves','maximum S cost',max_cost)
(R/'upper-tree.json').write_text(json.dumps({'nodes':nodes,'leaves':leaves,'max_S_cost':max_cost},indent=2))
