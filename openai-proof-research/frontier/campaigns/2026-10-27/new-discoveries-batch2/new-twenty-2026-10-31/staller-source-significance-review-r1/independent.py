import json,resource,time
from functools import lru_cache
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
t=time.monotonic(); V=frozenset(range(7)); E=[(0,1),(0,5),(1,2),(1,6),(2,3),(3,4),(4,5),(5,6)]
N=tuple(frozenset({v}|{b for a,b in E if a==v}|{a for a,b in E if b==v}) for v in V)
def won(s):return any(n<=s for n in N)
def dwon(d):return all(n&d for n in N)
@lru_cache(None)
def value(s,d,st):
 assert not s&d
 if won(s): return 0
 if dwon(d):return float('inf')
 a=V-s-d
 if not a:return float('inf')
 vals=[(1+value(s|{v},d,False)) if st else value(s,d|{v},True) for v in a]
 return (min if st else max)(vals)
@lru_cache(None)
def budget(s,d,st,b):
 if won(s):return True
 if dwon(d):return False
 a=V-s-d
 if not a:return False
 if st:return b>0 and any(budget(s|{v},d,False,b-1) for v in a)
 return all(budget(s,d|{v},True,b) for v in a)
def upper(s,d,st):
 if won(s):return {'S':sorted(s),'D':sorted(d),'win':next(sorted(n) for n in N if n<=s)}
 a=sorted(V-s-d)
 if st:
  v=min(a,key=lambda v:value(s|{v},d,False));return {'S_move':v,'next':upper(s|{v},d,False)}
 return {'D_responses':{str(v):upper(s,d|{v},True) for v in a}}
# Independently generate response table which blocks EVERY neighborhood after every third move.
lower=[]
for x in sorted(V):
 for y in sorted(V-{x}):
  table={}
  for z in sorted(V-{x,y}):
   opts=[w for w in sorted(V-{x,y,z}) if all(not won(frozenset({x,z,u})) for u in V-{x,y,z,w})]
   if not opts:break
   table[z]=opts[0]
  if len(table)==5: lower.append({'S1':x,'D1':y,'S2_D2':table});break
assert len(lower)==7
# All disjoint states: prove recurrence variants agree, including terminal D-win and empty board.
states=0
import itertools
for assignment in itertools.product(range(3),repeat=7):
 s=frozenset(i for i,c in enumerate(assignment) if c==1);d=frozenset(i for i,c in enumerate(assignment) if c==2)
 for st in [False,True]:
  v=value(s,d,st)
  for b in range(5):assert budget(s,d,st,b)==(v<=b)
  states+=1
out={'edges':E,'neighborhoods':[sorted(n) for n in N],'degrees':[len(n)-1 for n in N],'S_value':value(frozenset(),frozenset(),True),'D_value':str(value(frozenset(),frozenset(),False)),'first_S_values':{str(v):str(1+value(frozenset({v}),frozenset(),False)) for v in V},'S_budgets':[budget(frozenset(),frozenset(),True,b) for b in range(5)],'all_disjoint_states_times_turns':states,'lower_table':lower,'upper':upper(frozenset(),frozenset(),True),'seconds':time.monotonic()-t,'resource_caps':{'CPU_seconds':30,'AS_MiB':512,'wall_external_seconds':40,'affinity':'at most 2 CPUs'}}
Path(__file__).with_name('independent-results.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k not in ['upper','lower_table']},indent=2))
