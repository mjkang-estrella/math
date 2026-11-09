"""Fresh independent coordinate implementation and arithmetic assertions."""
import json
from fractions import Fraction
from math import comb
from functools import cache
from itertools import combinations_with_replacement
from pathlib import Path
L=Path(__file__).resolve().parent
D=json.loads((L/'computations.json').read_text())
def play(x,l,dev=False):
 x=tuple(x);out=[x]
 while x.count(0)<2:
  if dev and len(out)==1:i=1 if x==(4,4,5) else 0
  else:
   eligible=[j for j,v in enumerate(x) if v%l==0]
   value=min(x[j] for j in eligible) if eligible else max(x)
   i=max(j for j,v in enumerate(x) if v==value)
  assert all(v>0 for j,v in enumerate(x) if j!=i)
  y=tuple(v-(j!=i) for j,v in enumerate(x));assert sum(x)-sum(y)==len(x)-1
  x=y;out.append(x)
 return out
expected=[[(4,4,5),(3,3,5),(2,3,4),(1,3,3),(0,2,3),(0,1,2),(0,0,1)],[(4,4,5),(3,4,4),(3,3,3),(2,2,3),(1,1,3),(0,0,3)]]
assert [play((4,4,5),3,d) for d in [False,True]]==expected
rows=[]
for n in range(3,16):
 for l in range(3,25):
  a=(n-2)*l+1;b=(n-1)*l-1;x=(a,)*(n-1)+(b,)
  g=play(x,l);d=play(x,l,True)
  assert (len(g)-1,len(d)-1)==((n-1)*l,(n-1)*l-1)
  for i in range(1,n):
   q=(n-1-i)*l;t=1+(i-1)*l
   assert sorted(g[t])==sorted([q]*(n-i)+[q+l]*(i-1)+[q+l-1])
   assert sorted(d[t])==sorted([q]*(n-1-i)+[q+1,q+l-2]+[q+l]*(i-1))
  rows.append([n,l,len(g)-1,len(d)-1])
assert len(rows)==286
for row,count in zip(D['search'],[0,0,19,2]):
 assert row['positions']==comb(row['B']+row['n'],row['n'])
 assert row['violating_player_position_pairs']==count
assert D['robust']['all_terminal_length_loser_pairs']==[[7,1]]
assert Fraction(D['robust']['payoff'])==1
examples=[]
for x,C in [((4,4,5),7),((2,4,4),6),((5,5,6),9)]:
 lengths=[len(play(x,3,d))-1 for d in [False,True]]
 assert sum(x)//2<C
 rewards=[str(Fraction(-(C-t)) if t%3==0 else Fraction(C-t,2)) for t in lengths]
 examples.append(dict(x=x,C=C,mass=sum(x),bound=sum(x)//2,lengths=lengths,rewards=rewards))
assert examples[0]['rewards']==['-1','1']
assert examples[1]['rewards']==['1/2','1']
def legal_moves(x):
 if x.count(0)>1:return []
 return [(j,tuple(v-(k!=j) for k,v in enumerate(x))) for j in range(len(x)) if all(v>0 for k,v in enumerate(x) if k!=j)]
def pivot(x,l):
 vals=[v for v in x if v%l==0];v=min(vals) if vals else max(x)
 return max(j for j,w in enumerate(x) if w==v)
def reward(t,p,l,C):return Fraction(t-C) if t%l==p else Fraction(C-t,l-1)
policy={}
@cache
def minimax(x,t):
 if x.count(0)>1:return reward(t,0,3,9)
 choices=legal_moves(x)
 if t%3 and any(v%3==0 for v in x):choices=[pair for pair in choices if pair[0]==pivot(x,3)]
 values=[(minimax(y,t+1),j,y) for j,y in choices]
 if t%3==0:
  value=max(v for v,j,y in values);policy[x,t]=next((j,y) for v,j,y in values if v==value)
  return value
 return min(v for v,j,y in values)
assert minimax((5,5,6),0)==1
leaves=set()
def traverse(x,t):
 if x.count(0)>1:leaves.add((t,t%3));return
 choices=legal_moves(x)
 if t%3==0:choices=[policy[x,t]]
 elif any(v%3==0 for v in x):choices=[pair for pair in choices if pair[0]==pivot(x,3)]
 for j,y in choices:traverse(y,t+1)
traverse((5,5,6),0);assert leaves=={(7,1)}
independent_search=[]
for n,l,B in [(3,2,12),(4,2,8),(3,3,10),(4,3,7)]:
 @cache
 def solve(x,t,p):
  if x.count(0)>1:
   v=reward(t,p,l,n*B+1);return v,v
  choices=[(j,tuple(sorted(y))) for j,y in legal_moves(x)]
  forced=pivot(x,l)
  vals={j:solve(y,t+1,p) for j,y in choices}
  baseline=vals[forced][0]
  optimum=max(v[1] for v in vals.values()) if t%l==p else vals[forced][1]
  return baseline,optimum
 count=0;states=0
 for x in combinations_with_replacement(range(B+1),n):
  states+=1
  for p in range(l):
   g,b=solve(x,0,p);count+=b>g
 independent_search.append(dict(n=n,l=l,B=B,positions=states,violating_player_position_pairs=count))
for row,old in zip(independent_search,D['search']):
 assert all(old[k]==v for k,v in row.items())
out=dict(status='PASS',literal_traces=expected,examples=examples,family=rows,search=independent_search,robust_leaves=sorted(leaves),independent_minimax_value=str(minimax((5,5,6),0)),numeric_scope='All computed game numbers in manuscript; bibliographic identifiers, dates, source line numbers and formal tool versions are transcribed metadata, not experimental results.')
(L/'numeric-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: independent literal traces, family, bounds, rewards and search arithmetic')
