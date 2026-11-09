# Derangement representation (Ashofteh-Iradmusa arXiv:2404.13424, Def. 1): injective pi: V -> S_k with
# u~v iff pi(u)(i) != pi(v)(i) for all i. Test drn(G) <= n for all graphs of order n (graph6 input: connected graphs;
# complements of connected graphs with disconnected complement are added so every graph of order n is covered once).
import sys,time,itertools
def g6(s):
    s=s.strip(); n=ord(s[0])-63; bits=[]
    for ch in s[1:]:
        v=ord(ch)-63; bits+=[(v>>(5-i))&1 for i in range(6)]
    A=[[0]*n for _ in range(n)]; t=0
    for j in range(1,n):
        for i in range(j):
            A[i][j]=A[j][i]=bits[t]; t+=1
    return n,A
def connected(n,A):
    seen={0}; st=[0]
    while st:
        u=st.pop()
        for v in range(n):
            if A[u][v] and v not in seen: seen.add(v); st.append(v)
    return len(seen)==n
def embed(n,A,k,deadline):
    # order vertices: BFS-ish by degree
    order=sorted(range(n),key=lambda v:-sum(A[v]))
    rows=[None]*n
    def cand(i):
        v=order[i]
        adjrows=[rows[order[j]] for j in range(i) if A[v][order[j]]]
        non=[rows[order[j]] for j in range(i) if not A[v][order[j]]]
        perm=[0]*k; used=[False]*k
        def colrec(c,agreed):
            if c==k:
                if agreed==(1<<len(non))-1: yield tuple(perm)
                return
            # prune: unsatisfied non-adjacent rows need agreement in remaining columns
            if bin(((1<<len(non))-1)&~agreed).count('1')>0 and k-c==0: return
            for x in range(k):
                if used[x] or any(r[c]==x for r in adjrows): continue
                na=agreed
                for t,r in enumerate(non):
                    if r[c]==x: na|=1<<t
                used[x]=True; perm[c]=x
                yield from colrec(c+1,na)
                used[x]=False
        yield from colrec(0,0)
    def rec(i):
        if time.time()>deadline: raise TimeoutError
        if i==n: return True
        seen=set(rows[order[j]] for j in range(i))
        for p in cand(i):
            if p in seen: continue
            rows[order[i]]=p
            if rec(i+1): return True
        rows[order[i]]=None
        return False
    rows[order[0]]=tuple(range(k))
    return rows if rec(1) else None
if __name__=='__main__':
    path=sys.argv[1]; lo,hi=int(sys.argv[2]),int(sys.argv[3]); budget=float(sys.argv[4])
    lines=open(path).read().split()
    t0=time.time(); done=lo; fails=[]
    try:
        for idx in range(lo,min(hi,len(lines))):
            n,A=g6(lines[idx])
            todo=[A]
            B=[[0 if i==j else 1-A[i][j] for j in range(n)] for i in range(n)]
            if not connected(n,B): todo.append(B)
            for M in todo:
                ok=False
                for k in range(n,0,-1):
                    if embed(n,M,k,t0+budget): ok=True; break
                    if k<=n-1: pass
                if not ok: fails.append((idx,M)); print('FAIL drn>n',lines[idx],'complement' if M is not A else '',flush=True)
            done=idx+1
    except TimeoutError:
        pass
    print('file',path.split('/')[-1],'completed [%d,%d) of %d, failures %d, %.1fs'%(lo,done,len(lines),len(fails),time.time()-t0),flush=True)
