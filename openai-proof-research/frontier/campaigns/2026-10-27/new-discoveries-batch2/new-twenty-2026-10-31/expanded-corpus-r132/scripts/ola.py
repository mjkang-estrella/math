# OLA encoding (Richman-Zhang-Matsen) and exact expected OLA distance over all SPR moves.
# Tree: nested tuples, leaves are ints 0..n-1.  Internal node with child clades A,B gets label -max(min A, min B).
import sys,random,json
def leaves(t): return [t] if isinstance(t,int) else leaves(t[0])+leaves(t[1])
def restrict(t,keep):
    if isinstance(t,int): return t if t in keep else None
    a=restrict(t[0],keep); b=restrict(t[1],keep)
    if a is None: return b
    if b is None: return a
    return (a,b)
def code(t):
    n=len(leaves(t)); out=[]
    # compute via parent pointers on full tree with clade minima restricted to <=i: do it directly by restriction (O(n^2))
    for i in range(1,n):
        ti=restrict(t,set(range(i+1)))
        # find sister of leaf i
        def find(x):
            if isinstance(x,int): return None
            if x[0]==i: return x[1]
            if x[1]==i: return x[0]
            r=find(x[0])
            return r if r is not None else find(x[1])
        s=find(ti)
        if isinstance(s,int): out.append(s)
        else: out.append(-max(min(leaves(s[0])),min(leaves(s[1]))))
    return out
def code_fast(t):
    # O(n log n)-ish: for each leaf i, sister clade in T_i = among the path from i to root, the first ancestor whose
    # other side contains a leaf < i; sister = that other side restricted to leaves < i.
    par={}; side={}
    def walk(x,p):
        if isinstance(x,int): par[('L',x)]=p; return ('L',x)
        node=('N',id(x)); par[node]=p
        a=walk(x[0],node); b=walk(x[1],node); side[node]=(x[0],x[1]); return node
    nodes={}
    def build(x):
        if isinstance(x,int): return {'leaf':x,'min':x}
        a=build(x[0]); b=build(x[1]); d={'c':(a,b),'min':min(a['min'],b['min'])}; a['p']=d; b['p']=d; return d
    root=build(t); root['p']=None
    leafnode={}
    def collect(d):
        if 'leaf' in d: leafnode[d['leaf']]=d
        else: collect(d['c'][0]); collect(d['c'][1])
    collect(root)
    n=len(leafnode); out=[]
    def restricted(d,i):
        # restricted subtree of d to leaves < i: return either a leaf int or label of internal node
        while True:
            if 'leaf' in d: return d['leaf']
            a,b=d['c']
            if a['min']<i and b['min']<i: return -max(a['min'],b['min'])
            d=a if a['min']<i else b
    for i in range(1,n):
        x=leafnode[i]
        while True:
            p=x['p']; other=p['c'][1] if p['c'][0] is x else p['c'][0]
            if other['min']<i: out.append(restricted(other,i)); break
            x=p
    return out
def height(t): return 0 if isinstance(t,int) else 1+max(height(t[0]),height(t[1]))
def subtrees_paths(t,path=()):
    yield path,t
    if not isinstance(t,int):
        yield from subtrees_paths(t[0],path+(0,)); yield from subtrees_paths(t[1],path+(1,))
def get(t,p):
    for c in p: t=t[c]
    return t
def prune(t,p):
    # remove subtree at path p (p nonempty), suppress parent
    if len(p)==1: return t[1-p[0]]
    c=p[0]; sub=prune(t[c],p[1:])
    return (sub,t[1]) if c==0 else (t[0],sub)
def regraft_all(t,X):
    # all trees obtained by attaching X on every edge of t, including above the root
    res=[(X,t)]
    if not isinstance(t,int):
        for a in regraft_all(t[0],X)[0:]: res.append((a,t[1]))
        for b in regraft_all(t[1],X): res.append((t[0],b))
    return res
def canon(t):
    if isinstance(t,int): return t
    a=canon(t[0]); b=canon(t[1])
    return (a,b) if min(leaves(a))<min(leaves(b)) else (b,a)
def spr_stats(t):
    ct=canon(t); c0=code_fast(ct); tot=0; cnt=0; distinct={}
    for p,X in subtrees_paths(ct):
        if not p: continue
        rest=prune(ct,p)
        for t2 in regraft_all(rest,X):
            t2c=canon(t2)
            if t2c==ct: continue
            c=code_fast(t2c); d=sum(1 for a,b in zip(c0,c) if a!=b)
            tot+=d; cnt+=1; distinct[t2c]=d
    return dict(n=len(c0)+1,height=height(ct),moves=cnt,mean_moves=tot/cnt,distinct=len(distinct),mean_distinct=sum(distinct.values())/len(distinct))
def balanced(labels):
    if len(labels)==1: return labels[0]
    h=len(labels)//2; return (balanced(labels[:h]),balanced(labels[h:]))
if __name__=='__main__':
    # self-test: code_fast == code, bijection count for n=5
    import itertools
    rnd=random.Random(0)
    def rand_tree(lbls):
        if len(lbls)==1: return lbls[0]
        k=rnd.randint(1,len(lbls)-1); return (rand_tree(lbls[:k]),rand_tree(lbls[k:]))
    for _ in range(200):
        L=list(range(rnd.randint(2,12))); rnd.shuffle(L); t=rand_tree(L)
        assert code(t)==code_fast(t)
    print('selftest ok')
    mode=sys.argv[1]
    for h in range(2,int(sys.argv[2])+1):
        n=2**h; L=list(range(n))
        if mode=='natural': pass
        elif mode=='random': rnd.shuffle(L)
        elif mode=='bitrev': L=[int(format(i,'0%db'%h)[::-1],2) for i in range(n)]
        r=spr_stats(balanced(L)); r['ratio']=r['mean_moves']/r['height']; print(json.dumps(r),flush=True)
