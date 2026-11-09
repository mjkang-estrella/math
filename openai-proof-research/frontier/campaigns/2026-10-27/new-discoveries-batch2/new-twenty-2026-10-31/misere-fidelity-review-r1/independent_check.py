"""Independent finite bipartite SET game model, with explicit player identities.
Validation only; the Lean kernel proof is the formal certificate.
"""
from functools import cache
from pathlib import Path
import json

def G(left=(),right=()):return (frozenset(left),frozenset(right))
def I(*opts):return G(opts,opts)
Z=I(); S=I(Z); T=I(S); U=I(Z,S); B=I(U); V=I(S,T); C=I(V)
@cache
def adj(g):
 l,r=g
 if not l and not r:return S
 if not l:return G([adj(x) for x in r],[Z])
 if not r:return G([Z],[adj(x) for x in l])
 return G([adj(x) for x in r],[adj(x) for x in l])
@cache
def add(g,h):
 return G([add(x,h) for x in g[0]]+[add(g,x) for x in h[0]],
          [add(x,h) for x in g[1]]+[add(g,x) for x in h[1]])
@cache
def winner(g,turn):
 # Left=0, Right=1. No legal move: CURRENT player wins in misere.
 options=g[turn]
 if not options:return turn
 if any(winner(h,1-turn)==turn for h in options):return turn
 return 1-turn

def outcome(g):
 l=winner(g,0);r=winner(g,1)
 return 'L' if l==r==0 else 'R' if l==r==1 else 'N' if (l,r)==(0,1) else 'P'
assert [adj(x) for x in [Z,S,U,B]]==[S,T,V,C]
positions={'Z':Z,'S':S,'T':T,'U':U,'B':B,'V':V,'C':C,
 'S+S':add(S,S),'S+T':add(S,T),'S+U':add(S,U),'T+U':add(T,U),
 'S+B':add(S,B),'T+B':add(T,B)}
expected=dict(zip(positions,['N','P','N','N','P','N','P','N','P','N','N','N','P']))
actual={k:outcome(v) for k,v in positions.items()}
assert actual==expected
arrows={k: {'outcome':outcome(add(b,adj(a))), 'Left_wins_moving_second':winner(add(b,adj(a)),1)==0,'Right_wins_moving_second':winner(add(b,adj(a)),0)==1} for k,a,b in [('S->B',S,B),('B->Z',B,Z),('S->Z',S,Z)]}
assert [v['Left_wins_moving_second'] for v in arrows.values()]==[True,True,False]
assert all(v['Left_wins_moving_second']==v['Right_wins_moving_second'] for v in arrows.values())
result={'model':'bipartite frozensets, four-case adjoint, explicit turn winner','outcomes':actual,'arrows':arrows}
Path(__file__).with_name('independent-check.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
