"""Mirror of Lean `step`/`norm`/`ins` (TabMinors.lean) to emit per-level literal weighted lists for T1, T2."""
import sys
sys.path.insert(0,'scripts')
from verify_minors import delete  # same jeu de taquin as minors.py
def ins(p,L):
    for idx,q in enumerate(L):
        if q[0]==p[0]: return L[:idx]+[(q[0],q[1]+p[1])]+L[idx+1:]
    return L+[p]
def norm(L):
    acc=[]
    for p in reversed(L): acc=ins(p,acc)   # foldr ins []
    return acc
def size(T): return sum(len(r) for r in T)
def step(L): return norm([(delete(t,i+1),c) for (t,c) in L for i in range(size(t))])
def lean(L): return '[' + ', '.join('(%s, %d)'%('['+', '.join('['+', '.join(map(str,r))+']' for r in t)+']',c) for t,c in L) + ']'
T1=((1,5,7,8,12),(2,),(3,),(4,),(6,),(9,),(10,),(11,))
T2=((1,2,3,7,10,11),(4,),(5,),(6,),(8,),(9,),(12,))
out=[]
for name,T in [('A',T1),('B',T2)]:
    L=[(T,1)]
    for lvl in range(1,9):
        L=step(L); out.append(f'def {name}{lvl} : List (Tab × ℕ) := {lean(L)}')
        print(name,lvl,len(L),file=sys.stderr)
open('lean/levels.txt','w').write('\n'.join(out)+'\n')
