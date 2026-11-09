from pathlib import Path
from functools import lru_cache
import resource,os,json
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(15,15));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=Path(__file__).parent; E=[(0,1),(0,5),(1,2),(1,6),(2,3),(3,4),(4,5),(5,6)];N=[{i} for i in range(7)]
for a,b in E:N[a].add(b);N[b].add(a)
@lru_cache(None)
def W(s,d,turn,b):
 s=set(s);d=set(d);free=set(range(7))-s-d
 if any(z<=s for z in N):return True
 if not free:return False
 if turn:return b>0 and any(W(tuple(sorted(s|{v})),tuple(sorted(d)),False,b-1) for v in free)
 return all(W(tuple(sorted(s)),tuple(sorted(d|{v})),True,b) for v in free)
rows=[]
for a in range(7):
 d=next(v for v in range(7) if v!=a and not W((a,),(v,),True,2));replies={}
 for b in set(range(7))-{a,d}:
  e=next(v for v in set(range(7))-{a,b,d} if not W(tuple(sorted([a,b])),tuple(sorted([d,v])),True,1));replies[b]=e
  assert all(not any(z<={a,b,c} for z in N) for c in set(range(7))-{a,b,d,e})
 rows.append({'S1':a,'D1':d,'S2_to_D2':replies})
assert W((),(),True,4) and not W((),(),True,3)
(p/'ordinary-certificate.json').write_text(json.dumps({'closed_neighborhoods':[sorted(z) for z in N],'lower_bound_response_table':rows,'W4':True,'W3':False},indent=2)+'\n');print(json.dumps(rows))
tree=json.loads((p/'strategy.log').read_text().split('\n',1)[1]);nodes=0;leaves=0

def verify(t,s,d,turn):
 global nodes,leaves
 nodes+=1;free=set(range(7))-s-d
 assert len(s)<=4
 if 'win' in t:
  assert t['win']==sum(1<<i for i in s) and any(z<=s for z in N);leaves+=1;return
 if turn:
  v=t['S'];assert v in free;verify(t['next'],s|{v},d,False)
 else:
  assert set(map(int,t['D']))==free
  for v,child in t['D'].items():verify(child,s,d|{int(v)},True)
verify(tree,set(),set(),True)
print('UPPER_TREE_PASS',nodes,'nodes',leaves,'leaves; complete legal response coverage; at most4 Staller moves')
