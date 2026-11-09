"""Independent implementation. No discovery imports. All rewards use exact rationals."""
from functools import lru_cache
from itertools import combinations_with_replacement
from fractions import Fraction
import json

def terminal(x): return x.count(0)>=2
def successors(x):
 if terminal(x): return []
 return [(i,tuple(sorted(v-(j!=i) for j,v in enumerate(x)))) for i in range(len(x)) if all(v>0 for j,v in enumerate(x) if j!=i)]
def gm(x,l):
 eligible=[(v,-i,i) for i,v in enumerate(x) if v%l==0]
 return min(eligible)[2] if eligible else len(x)-1

def trace(x,l,deviate=False):
 rows=[]; t=0
 while not terminal(x):
  i=0 if deviate and t==0 else gm(x,l)
  choices=dict(successors(x)); assert i in choices
  rows.append({'t':t,'player':t%l,'x':x,'keep':x[i],'index':i,'multiple':any(v%l==0 for v in x)})
  x=choices[i]; t+=1
 rows.append({'t':t,'player':t%l,'x':x,'terminal':True})
 return rows

def reward(t,loser,p,l,C): return Fraction(-(C-t)) if p==loser else Fraction(C-t,l-1)

def search(n,l,B):
 C=n*B+1
 @lru_cache(None)
 def solve(x,t,p,br):
  if terminal(x): return reward(t,t%l,p,l,C)
  succ=successors(x)
  if not br or t%l!=p: succ=[(i,y) for i,y in succ if i==gm(x,l)]
  return max(solve(y,t+1,p,br) for _,y in succ)
 count=0; examples=[]; positions=0
 for x in combinations_with_replacement(range(B+1),n):
  positions+=1
  for p in range(l):
   g=solve(x,0,p,False); b=solve(x,0,p,True)
   if b>g:
    count+=1
    if len(examples)<8: examples.append({'x':x,'p':p,'gm':str(g),'best':str(b)})
 return dict(n=n,l=l,B=B,positions=positions,violating_player_position_pairs=count,examples=examples)

out={'traces':{str(x):{'gm':trace(x,3),'deviation':trace(x,3,True)} for x in [(4,4,5),(5,5,6)]}}
assert out['traces']['(4, 4, 5)']['gm'][-1]['t']==6
assert out['traces']['(4, 4, 5)']['deviation'][-1]['t']==5
# Convention-free minimax uses actual payoff and absolute time, no tuple ordering surrogate.
C=9
@lru_cache(None)
def robust(x,t):
 if terminal(x): return reward(t,t%3,0,3,C),[{'t':t,'x':x,'terminal':True}]
 succ=successors(x)
 if t%3!=0 and any(v%3==0 for v in x): succ=[(i,y) for i,y in succ if i==gm(x,3)]
 vals=[]
 for i,y in succ:
  v,path=robust(y,t+1); vals.append((v,[{'t':t,'player':t%3,'x':x,'keep':x[i],'multiple':any(v%3==0 for v in x)}]+path))
 return (max if t%3==0 else min)(vals,key=lambda z:z[0])
v,path=robust((5,5,6),0)
out['robust']={'C':C,'payoff':str(v),'worst_path':path}; assert v==1
assert all(r['multiple'] for r in out['traces']['(5, 5, 6)']['gm'][:-1])
# Invariant checks at every block boundary, and numerical stress of all terminal lengths.
count=0
for n in range(3,16):
 for l in range(3,25):
  a=(n-2)*l+1;b=(n-1)*l-1;x=(a,)*(n-1)+(b,)
  g=trace(x,l); d=trace(x,l,True)
  assert g[-1]['t']==(n-1)*l and d[-1]['t']==(n-1)*l-1
  for i in range(1,n):
   q=(n-1-i)*l;t=1+(i-1)*l
   I=tuple(sorted([q]*(n-i)+[q+l]*(i-1)+[q+l-1]))
   J=tuple(sorted([q]*(n-1-i)+[q+1,q+l-2]+[q+l]*(i-1)))
   assert g[t]['x']==I and d[t]['x']==J
  count+=1
out['family_checks']=count
out['search']=[search(n,l,B) for n,l,B in [(3,2,12),(4,2,8),(3,3,10),(4,3,7)]]
assert all(s['violating_player_position_pairs']==0 for s in out['search'] if s['l']==2)
out['smaller']={'gm':trace((2,4,4),3),'deviation':trace((2,4,4),3,True)}
# Traverse every adversarial branch under one fixed maximizing policy for P0.
tree=[]; leaves=set()
def visit(x,t):
 if terminal(x):
  leaves.add((t,t%3));return
 succ=successors(x)
 if t%3==0:
  goal=robust(x,t)[0]
  succ=next([pair] for pair in succ if robust(pair[1],t+1)[0]==goal)
 elif any(v%3==0 for v in x): succ=[pair for pair in succ if pair[0]==gm(x,3)]
 tree.append({'x':x,'t':t,'keeps':[x[i] for i,y in succ]})
 for i,y in succ: visit(y,t+1)
visit((5,5,6),0)
out['robust']['policy_tree']=tree
out['robust']['all_terminal_length_loser_pairs']=sorted(leaves)
assert all(t<=7 and loser!=0 for t,loser in leaves)
print(json.dumps(out,indent=2))
