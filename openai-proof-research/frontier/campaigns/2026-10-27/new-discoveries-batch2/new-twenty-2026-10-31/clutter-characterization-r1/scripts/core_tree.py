"""Find a small unsat core of blocker members and a small decision tree certificate
for: for every p (p(X)∈X for all edges X), some core Y is 'dead' (every v∈Y is killed:
exists X with X∩Y={v} and p(X)=v).  Exact, exhaustive; writes JSON certificate."""
import sys, json, itertools
A=json.load(open(sys.argv[1]))[sys.argv[2]][int(sys.argv[3])]
n=len(A[0]); C=[frozenset(j for j in range(n) if r[j]) for r in A]
def transversal(S): return all(S & X for X in C)
B=[]
for m in range(1<<n):
    S=frozenset(j for j in range(n) if m>>j&1)
    if transversal(S) and all(not transversal(S-{v}) for v in S): B.append(S)
def dead(Y,p):  # p: dict edge-index -> value (partial ok)
    return all(any(len(C[i]&Y)==1 and v in C[i] and p.get(i)==v for i in range(len(C))) for v in Y)
def unsat(Ys):
    for p in itertools.product(*[sorted(X) for X in C]):
        pd=dict(enumerate(p))
        if not any(dead(Y,pd) for Y in Ys): return False
    return True
assert unsat(B)
# greedy core reduction, try removing larger sets first
core=sorted(B,key=lambda Y:(-len(Y),sorted(Y)))
i=0
while i<len(core):
    t=core[:i]+core[i+1:]
    if unsat(t): core=t
    else: i+=1
print('blocker size',len(B),'core size',len(core),[sorted(Y) for Y in core],file=sys.stderr)
# decision tree: choose edge to branch minimizing leaves (greedy by most-constraining)
import functools
def tree(pd):
    for j,Y in enumerate(core):
        if dead(Y,pd): return {'leaf':sorted(Y)}
    free=[i for i in range(len(C)) if i not in pd]
    best=None
    for i in free:
        # heuristic score: number of branches that immediately close
        s=sum(1 for v in C[i] if any(dead(Y,{**pd,i:v}) for Y in core))
        if best is None or s>best[0]: best=(s,i)
    i=best[1]
    return {'edge':i,'children':{v:tree({**pd,i:v}) for v in sorted(C[i])}}
T=tree({})
def leaves(t): return 1 if 'leaf' in t else sum(leaves(c) for c in t['children'].values())
print('tree leaves',leaves(T),file=sys.stderr)
json.dump({'edges':[sorted(X) for X in C],'core':[sorted(Y) for Y in core],'blocker':[sorted(Y) for Y in B],'tree':T},open(sys.argv[4],'w'))
