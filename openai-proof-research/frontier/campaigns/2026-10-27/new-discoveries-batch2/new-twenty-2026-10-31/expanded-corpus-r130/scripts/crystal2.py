# Independent re-implementation of Lecouvey-Lenart-Schultze (arXiv:2110.15394v2) Defs 3.1, 3.2, 4.1, 4.3, 5.1
# for type A_{n-1}; roots (a,b), 1<=a<b<=n, Kostant partition = dict root->mult (tuple over sorted roots).
import itertools, functools
class Model:
    def __init__(s,n):
        s.n=n; s.roots=[(a,b) for a in range(1,n+1) for b in range(a+1,n+1)]; s.idx={r:j for j,r in enumerate(s.roots)}
    def word(s,al,i,star):
        # returns reduced word as list of (sign, root) ; sign +1 or -1
        if star:
            order=sorted(s.roots,key=lambda r:(r[1],-r[0]))
            sign=lambda r: 1 if r[0]==i+1 else (-1 if r[0]==i else 0)
        else:
            order=sorted(s.roots,key=lambda r:(-r[0],r[1]))
            sign=lambda r: 1 if r[1]==i else (-1 if r[1]==i+1 else 0)
        st=[]
        for r in order:
            g=sign(r)
            if not g: continue
            for _ in range(al[s.idx[r]]):
                if g==1 and st and st[-1][0]==-1: st.pop()
                else: st.append((g,r))
        return st
    def counts(s,al,i):
        W=s.word(al,i,False); Ws=s.word(al,i,True)
        a=sum(1 for g,_ in W if g==1); b=sum(1 for g,_ in W if g==-1)
        as_=sum(1 for g,_ in Ws if g==1); bs=sum(1 for g,_ in Ws if g==-1)
        return W,Ws,a,b,as_,bs
    def move(s,al,rem,add):
        l=list(al); l[s.idx[rem]]-=1
        if add is not None: l[s.idx[add]]+=1
        return tuple(l)
    @functools.lru_cache(None)
    def e(s,al,i):
        """returns (result or None, blocked) ; blocked=True iff e_i(al)=0 but hat e_i(al)!=0 (acts on simple root)"""
        W,Ws,a,b,as_,bs=s.counts(al,i)
        if bs<=a and b>0:
            r=[r for g,r in W if g==-1][0]   # leftmost -
            if r==(i,i+1): return None,True
            return s.move(al,r,(r[0],i)),False
        if bs>a:
            r=[r for g,r in Ws if g==-1][0]
            if r==(i,i+1): return None,True
            return s.move(al,r,(i+1,r[1])),False
        return None,False
    @functools.lru_cache(None)
    def f(s,al,i):
        W,Ws,a,b,as_,bs=s.counts(al,i)
        if bs<a:
            r=[r for g,r in W if g==1][-1]  # rightmost + in W_i^r, below (h,i)
            return s.move(al,r,(r[0],i+1))
        if bs>=a and as_>0:
            r=[r for g,r in Ws if g==1][-1]  # rightmost + in W*_i^r below (i+1,j)
            return s.move(al,r,(i,r[1]))
        return None
    def epow(s,al,i,k):
        for _ in range(k):
            al,_b=s.e(al,i)
            if al is None: return None
        return al
    def fpow(s,al,i,k):
        for _ in range(k):
            al=s.f(al,i)
            if al is None: return None
        return al
    def weight(s,al):
        w=[0]*(s.n+1)
        for c,(a,b) in zip(al,s.roots): w[a]+=c; w[b]-=c
        return w[1:]
    def BD(s,al,i,j):
        x,_=s.e(al,i); y,_=s.e(al,j)
        if x is None or y is None: return False
        return s.e(x,j)[1] and s.e(y,i)[1]
    def kostant(s,gamma):
        """all Kostant partitions of weight gamma (list, entries sum 0)"""
        n=s.n; res=[]
        R=s.roots
        def rec(j,cur,rem):
            if j==len(R):
                if all(x==0 for x in rem): res.append(tuple(cur))
                return
            a,b=R[j]
            # max multiplicity bounded by partial sums
            mx=sum(rem[:a]) if True else 0
            mx=max(0,min(sum(rem[:k]) for k in range(a,b)))
            for c in range(mx+1):
                r2=list(rem); r2[a-1]-=c; r2[b-1]+=c
                rec(j+1,cur+[c],r2)
        rec(0,[],list(gamma)); return res
