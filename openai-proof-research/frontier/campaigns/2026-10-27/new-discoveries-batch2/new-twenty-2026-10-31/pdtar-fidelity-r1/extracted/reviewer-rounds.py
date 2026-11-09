import json

def rounds(s,t,S):
 n=s+t
 N=[set(range(s,n)) if v<s else set(range(s)) for v in range(n)]
 O=set(S); history=[sorted(O)]
 O |= set().union(*(N[v] for v in S)) if S else set()
 history.append(sorted(O))
 while True:
  additions=set()
  for v in O:
   unseen=N[v]-O
   if len(unseen)==1: additions |= unseen
  Q=O|additions
  if Q==O: return len(O)==n,history
  O=Q; history.append(sorted(O))
cases=[(2,3,[0],True),(2,3,[2],False),(3,4,[0,3],True),(3,4,[0,1],True),(3,4,[0],False),(2,3,[],False),(3,4,[],False)]
for s,t,S,expected in cases:
 result,history=rounds(s,t,S)
 assert result==expected
 print(json.dumps(dict(s=s,t=t,S=S,PD=result,rounds=history)))
assert len({0}^{0,2})==1
print('TAR adjacency difference: [0] versus [0,2] has size 1')
