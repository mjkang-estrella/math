# Trail Trap solver (Buchanan et al. arXiv:2405.05195 rules): P1 places token and moves along an edge; P2 places token anywhere
# and moves along a different unused edge; then alternate moving own token along unused edges; first unable to move loses.
import sys
from functools import lru_cache
sys.setrecursionlimit(10000)
def grid(m,n):
    V=[(i,j) for i in range(m) for j in range(n)]; idx={v:k for k,v in enumerate(V)}
    E=[]
    for (i,j) in V:
        if i+1<m: E.append((idx[(i,j)],idx[(i+1,j)]))
        if j+1<n: E.append((idx[(i,j)],idx[(i,j+1)]))
    return len(V),E
def solve(nv,E,first_moves=None):
    inc=[[] for _ in range(nv)]
    for k,(a,b) in enumerate(E):
        inc[a].append((k,b)); inc[b].append((k,a))
    memo={}
    def win(used,me,opp):
        # player to move is at 'me'; returns True if player to move wins
        key=(used,me,opp)
        r=memo.get(key)
        if r is not None: return r
        r=False
        for k,b in inc[me]:
            if not used>>k&1:
                if not win(used|1<<k,opp,b):
                    r=True;break
        memo[key]=r
        return r
    def p2_wins_after(k1,head1):
        # P2 to choose any unused edge/direction; P2 wins iff some choice leaves P1 (at head1) losing
        u=1<<k1
        for k2,(a,b) in enumerate(E):
            if k2==k1: continue
            for (s,t) in ((a,b),(b,a)):
                if not win(u|1<<k2,head1,t): return (True,(s,t))
        return (False,None)
    moves=first_moves if first_moves is not None else [(k,s,t) for k,(a,b) in enumerate(E) for (s,t) in ((a,b),(b,a))]
    res=[]
    for (k,s,t) in moves:
        w,reply=p2_wins_after(k,t)
        res.append(((s,t),w,reply,len(memo)))
        print('P1 opening',(s,t),'P2 wins' if w else 'P1 WINS', 'reply',reply,'memo',len(memo),flush=True)
        if not w: break
    return res
if __name__=='__main__':
    m,n=int(sys.argv[1]),int(sys.argv[2])
    nv,E=grid(m,n)
    # reduce P1 openings by the grid's symmetry group (reflections)
    def img(v,f):
        i,j=divmod(v,n); 
        if f&1: i=m-1-i
        if f&2: j=n-1-j
        return i*n+j
    seen=set(); ops=[]
    for k,(a,b) in enumerate(E):
        for (s,t) in ((a,b),(b,a)):
            orb=min((img(s,f),img(t,f)) for f in range(4))
            if orb in seen: continue
            seen.add(orb); ops.append((k,s,t))
    print('grid',m,n,'V',nv,'E',len(E),'opening classes',len(ops),flush=True)
    r=solve(nv,E,ops)
    print('RESULT', 'P2-win' if all(x[1] for x in r) else 'P1-win')
