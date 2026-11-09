# Exhaustive small-instance check of Alishahi-Meunier Conjecture 1 (arXiv:1704.02921) for given q:
# path 0..N-1, partition into classes of size >= q-1; need disjoint q-stable S_1..S_q covering all but
# exactly q-1 vertices of each class, |S_i| pairwise differing by <=1, |S_i cap V_j| >= floor((|V_j|+1)/q)-1.
import sys, time
from functools import lru_cache
q=int(sys.argv[1]); Nmax=int(sys.argv[2]); Nmin=int(sys.argv[3]) if len(sys.argv)>3 else 1
strong = len(sys.argv)>4 and sys.argv[4]=='strong'
MMAX=int(sys.argv[7]) if len(sys.argv)>7 else 99
CH=int(sys.argv[5]) if len(sys.argv)>5 else 1; CI=int(sys.argv[6]) if len(sys.argv)>6 else 0   # also require |S_i cap V_j| <= |V_j|/q
def colorings(N):
    # restricted growth strings with every block size >= q-1, up to reversal
    seq=[0]*N; cnt=[]
    def rec(i,k):
        if i==N:
            if all(c>=q-1 for c in cnt): yield tuple(seq)
            return
        # prune: blocks needing more elements
        need=sum(max(0,q-1-c) for c in cnt)
        if need>N-i: return
        for c in range(min(k+1,MMAX)):
            if c==k:
                cnt.append(1); seq[i]=c
                yield from rec(i+1,k+1)
                cnt.pop()
            else:
                cnt[c]+=1; seq[i]=c
                yield from rec(i+1,k)
                cnt[c]-=1
    yield from rec(0,0)
def canon(s):
    mp={}; out=[]
    for c in s:
        if c not in mp: mp[c]=len(mp)
        out.append(mp[c])
    return tuple(out)
def check(col):
    N=len(col); m=max(col)+1
    size=[col.count(j) for j in range(m)]
    lb=[(size[j]+1)//q-1 for j in range(m)]
    covered=N-(q-1)*m
    lo=covered//q; hi=-(-covered//q)
    # remaining occurrences of each class after position i
    rem=[[0]*m for _ in range(N+1)]
    for i in range(N-1,-1,-1):
        rem[i]=rem[i+1][:]; rem[i][col[i]]+=1
    sys.setrecursionlimit(10000)
    @lru_cache(maxsize=None)
    def go(i,last,state,tot):
        # last: tuple of labels of previous q-1 vertices (q means X); state: per class tuple (x, c_1..c_q); tot: per-label totals
        if i==N:
            return all(state[j][0]==q-1 and all(state[j][1+t]>=lb[j] for t in range(q)) for j in range(m)) and all(lo<=t<=hi for t in tot)
        j=col[i]; st=state[j]
        for lab in range(q+1):
            if lab==q:
                if st[0]>=q-1: continue
                ns=(st[0]+1,)+st[1:]
                ntot=tot
            else:
                if lab in last: continue
                if tot[lab]>=hi: continue
                if strong and (st[1+lab]+1)*q>size[j]: continue
                ns=st[:1+lab]+(st[1+lab]+1,)+st[2+lab:]
                ntot=tot[:lab]+(tot[lab]+1,)+tot[lab+1:]
            # feasibility for class j: remaining occurrences after i
            r=rem[i+1][j]
            need_x=q-1-ns[0]
            need_c=sum(max(0,lb[j]-ns[1+t]) for t in range(q))
            if need_x+need_c>r or need_x>r: continue
            nstate=state[:j]+(ns,)+state[j+1:]
            nlast=(last+(lab,))[-(q-1):] if q>1 else ()
            if go(i+1,nlast,nstate,ntot): return True
        return False
    init_last=tuple([q]*(q-1))
    return go(0,init_last,tuple((0,)+(0,)*q for _ in range(m)),(0,)*q)
t0=time.monotonic()
for N in range(Nmin,Nmax+1):
    tested=0; seen=set(); fails=[]
    for col in colorings(N):
        rc=canon(col[::-1])
        if rc<col: continue  # reversal symmetry
        idx=hash(col)%CH if False else (sum((c+1)*(i+7) for i,c in enumerate(col))%CH)
        if idx!=CI: continue
        tested+=1
        if not check(col): fails.append(col); print('COUNTEREXAMPLE',q,N,col,flush=True)
    print('q',q,'N',N,'colorings_tested',tested,'fails',len(fails),'secs',round(time.monotonic()-t0,1),flush=True)
