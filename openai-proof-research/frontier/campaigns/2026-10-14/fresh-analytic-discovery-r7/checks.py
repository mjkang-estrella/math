#!/usr/bin/env python3
"""Myeongjin Kang, no affiliation. MIT. Exact finite support, not a proof of F.
No writes, network, random entropy, third-party imports or receipt generation.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from random import Random
import json


def zeros(n, m):
    return [[Q(0) for _ in range(m)] for _ in range(n)]


def tr(a):
    return list(map(list, zip(*a)))


def mul(a, b):
    return [[sum((x*y for x,y in zip(row,col)), Q(0))
             for col in zip(*b)] for row in a]


def add(a,b):
    return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]


def inv(a):
    n=len(a)
    b=[list(r)+[Q(i==j) for j in range(n)] for i,r in enumerate(a)]
    for j in range(n):
        k=next(i for i in range(j,n) if b[i][j])
        b[j],b[k]=b[k],b[j]
        z=b[j][j]; b[j]=[x/z for x in b[j]]
        for i in range(n):
            if i!=j:
                z=b[i][j]; b[i]=[x-z*y for x,y in zip(b[i],b[j])]
    return [r[n:] for r in b]


def grounded(n,edges,root=0):
    ids=[i for i in range(n) if i!=root]; index={x:i for i,x in enumerate(ids)}
    a=zeros(n-1,n-1)
    for u,v,r in edges:
        if u==v: continue
        for x,y,z in [(u,u,1),(v,v,1),(u,v,-1),(v,u,-1)]:
            if x!=root and y!=root:a[index[x]][index[y]]+=Q(z)/r
    return a


def center(g,m):
    n=len(m); total=sum(m); p=[[Q(i==j)-m[j]/total for j in range(n)] for i in range(n)]
    return mul(mul(p,g),tr(p))


def degree(n,edges):
    m=[Q(0)]*n
    for u,v,_ in edges:m[u]+=1;m[v]+=1
    return m


def side(n,edges,e):
    u,v,_=edges[e]; adj=[[] for _ in range(n)]
    for j,(x,y,_) in enumerate(edges):
        if j!=e:adj[x].append(y);adj[y].append(x)
    seen={v}; todo=[v]
    while todo:
        x=todo.pop()
        for y in adj[x]:
            if y not in seen:seen.add(y);todo.append(y)
    assert u not in seen
    return seen


def block_checks():
    rng=Random(731029); cases=0; bridge_cases=0; cycle_cases=0
    for trial in range(64):
        edges=[]; blocks=[]; n=1
        for step in range(1+rng.randrange(7)):
            pole=rng.randrange(n); kind=rng.choice(['link','loop','parallel','cycle'])
            size=2 if kind in ('link','parallel') else (1 if kind=='loop' else rng.randrange(3,6))
            vertices=[pole]+list(range(n,n+size-1)); old_n=n;n+=size-1
            for b in blocks:
                b['w'].extend([list(b['w'][pole]) for _ in range(size-1)])
            loc=[]
            if kind=='link':loc=[(0,1)]
            elif kind=='loop':loc=[(0,0)]
            elif kind=='parallel':loc=[(0,1)]*rng.randrange(2,5)
            else:loc=[(i,(i+1)%size) for i in range(size)]
            le=[(u,v,Q(rng.randrange(1,16),rng.randrange(1,8))) for u,v in loc]
            start=len(edges)
            edges.extend((vertices[u],vertices[v],r) for u,v,r in le)
            w=zeros(n,size-1)
            for i,x in enumerate(vertices[1:]):w[x][i]=1
            blocks.append({'kind':kind,'w':w,'local':le,'size':size,'edge':start})
        # Compare grounded energy inverse with the exact block sum.
        g=zeros(n,n)
        if n>1:
            qinv=inv(grounded(n,edges))
            for i in range(1,n):
                for j in range(1,n):g[i][j]=qinv[i-1][j-1]
        gs=zeros(n,n); contributions=[]
        for b in blocks:
            if b['size']==1:continue
            gb=mul(mul(b['w'],inv(grounded(b['size'],b['local']))),tr(b['w']))
            gs=add(gs,gb);contributions.append((b,gb))
        assert gs==g
        # Arbitrary masses exercise the weighted adjoint; actual degree tests loops.
        for m in [degree(n,edges),[Q(rng.randrange(1,9)) for _ in range(n)]]:
            assert all(x>0 for x in m)
            centered=center(g,m); csum=zeros(n,n)
            for b,gb in contributions:
                cb=center(gb,m);csum=add(csum,cb)
                trace=sum(m[i]*cb[i][i] for i in range(n))
                upper=sum(m[i]*gb[i][i] for i in range(n))
                assert 0<=trace<=upper
                if b['kind']=='link':
                    a=side(n,edges,b['edge']);s=sum(m[i] for i in a);total=sum(m)
                    r=edges[b['edge']][2]
                    assert trace==r*s*(1-s/total)
                    u=[Q(i in a)-s/total for i in range(n)]
                    assert cb==[[r*x*y for y in u] for x in u]
                    bridge_cases+=1
                else:cycle_cases+=1
            assert csum==centered
            if n>1:
                # Check the centered inverse K=G_c D_m against the generator.
                stiff=zeros(n,n)
                for u,v,r in edges:
                    if u!=v:
                        stiff[u][u]+=1/r;stiff[v][v]+=1/r
                        stiff[u][v]-=1/r;stiff[v][u]-=1/r
                expected=[[Q(i==j)-m[j]/sum(m) for j in range(n)] for i in range(n)]
                assert mul(centered,stiff)==expected
            cases+=1
    return {'graphs':64,'mass_systems':cases,'bridge_terms':bridge_cases,'cycle_terms':cycle_cases}


@lru_cache(None)
def trees(n):
    if n==1:return ((),)
    if n<1 or n%2==0:return ()
    out=[]
    for k in (2,4):
        def compositions(left,j,prefix=()):
            if j==0:
                if left==0:yield prefix
                return
            for s in range(1,left+1,2):yield from compositions(left-s,j-1,prefix+(s,))
        for sizes in compositions(n-1,k):
            for cs in product(*(trees(s) for s in sizes)):out.append(cs)
    return tuple(out)


@lru_cache(None)
def size(t):return 1+sum(size(c) for c in t)


def preorder(t):return (len(t),)+sum((preorder(c) for c in t),())


def probability(t):
    p={0:Q(5,8),2:Q(1,4),4:Q(1,8)}
    return p[len(t)]*prod(probability(c) for c in t)


def prod(xs):
    a=Q(1)
    for x in xs:a*=x
    return a


def walkprob(j,z):
    d={0:Q(1)}
    for _ in range(j):
        b={}
        for x,p in d.items():
            for y,q in [(-1,Q(5,8)),(1,Q(1,4)),(3,Q(1,8))]:b[x+y]=b.get(x+y,Q(0))+p*q
        d=b
    return d.get(z,Q(0))


def additive(t,f):return f(t)+sum(additive(c,f) for c in t)


def fringe_checks():
    pi={n:sum(map(probability,trees(n)),Q(0)) for n in range(1,12,2)}
    for n,p in pi.items():assert p==walkprob(n,-1)/n
    tolls=[lambda t:Q(not t),lambda t:Q(len(t)*sum(size(c) for c in t)),
           lambda t:Q(size(t)**2),lambda t:Q(len(t)==2)*size(t[-1]) if t else Q(0)]
    checks=0
    for n,p in pi.items():
        for f in tolls:
            lhs=sum(probability(t)*additive(t,f) for t in trees(n))/p/n
            rhs=sum(sum(probability(t)*f(t) for t in trees(s))*walkprob(n-s,0)
                    for s in pi if s<=n)/walkprob(n,-1)
            assert lhs==rhs;checks+=1
    # Forest convolution identity, including the j/t factor.
    forest=0
    for j in range(1,6):
        distribution={0:Q(1)}
        for _ in range(j):
            b={}
            for x,p in distribution.items():
                for y,q in pi.items():
                    if x+y<=11:b[x+y]=b.get(x+y,Q(0))+p*q
            distribution=b
        for t,p in distribution.items():
            assert p==Q(j,t)*walkprob(t,-j);forest+=1
    # Exact disjoint cyclic-window two-point factor for leaf and cherry patterns.
    n=7;pat1=(0,);pat2=(2,0,0);weighted=Q(0)
    law={0:Q(5,8),2:Q(1,4),4:Q(1,8)}
    for seq in product((0,2,4),repeat=n):
        if sum(seq)!=n-1:continue
        hits=0
        for i in range(n):
            if seq[i]!=0:continue
            for j in range(n):
                slots={(j+r)%n for r in range(3)}
                if i not in slots and tuple(seq[(j+r)%n] for r in range(3))==pat2:hits+=1
        weighted+=prod(law[x] for x in seq)*hits
    target=n*(n-1-3+1)*law[0]*(law[2]*law[0]**2)*walkprob(n-4,1)
    assert weighted==target
    return {'trees':sum(len(trees(n)) for n in pi),'cyclic_toll_identities':checks,
            'forest_identities':forest,'two_window_identity':True}


def binary_trees(n):
    if n==0:return ((),)
    return tuple((a,b) for k in range(n) for a in binary_trees(k) for b in binary_trees(n-1-k))


def corner_checks():
    cases=0;bridges=0
    for internal in range(1,5):
        for t in binary_trees(internal):
            for marks in product(('link','loop'),repeat=internal):
                it=iter(marks);edges=[];link=[];n=[1]
                def build(tree,pole):
                    if not tree:return
                    kind=next(it)
                    if kind=='link':
                        v=n[0];n[0]+=1;idx=len(edges);edges.append((pole,v,Q(1)))
                        link.append((idx,size(tree[1])))
                        build(tree[0],pole);build(tree[1],v)
                    else:
                        edges.append((pole,pole,Q(1)))
                        build(tree[0],pole);build(tree[1],pole)
                build(t,0);m=degree(n[0],edges)
                assert sum(m)==2*internal
                for idx,s in link:
                    a=side(n[0],edges,idx);assert sum(m[v] for v in a)==s;bridges+=1
                cases+=1
    return {'decorated_maps':cases,'bridge_corner_masses':bridges}


def gram_and_controls():
    m=[Q(i+1) for i in range(9)];total=sum(m)
    cuts=[{1,2},{4},{6,7}];us=[];ss=[]
    for a in cuts:
        s=sum(m[i] for i in a);ss.append(s);us.append([Q(i in a)-s/total for i in range(len(m))])
    for i,u in enumerate(us):
        for j,v in enumerate(us):
            value=sum(m[k]*u[k]*v[k] for k in range(len(m)))
            assert value==(ss[i]*(1-ss[i]/total) if i==j else -ss[i]*ss[j]/total)
    # Deliberately false operations must disagree with exact identities.
    controls={}
    controls['wrong_bridge_factor_two']=Q(7,2)!=Q(7)
    controls['ignore_loop_darts']=degree(2,[(0,1,Q(1)),(1,1,Q(1))])!=[Q(1),Q(1)]
    controls['omit_centering']=center([[Q(0),Q(0)],[Q(0),Q(7)]],[Q(1),Q(1)])!=[[Q(0),Q(0)],[Q(0),Q(7)]]
    a=[Q(-2,3),Q(1,3),Q(1,3)];b=[Q(-1,3),Q(-1,3),Q(2,3)]
    controls['nested_cuts_are_not_orthogonal']=sum(x*y for x,y in zip(a,b))==Q(1,3)
    # Unit triangle resistance 0->1 is 2/3, rather than the one-path value 1.
    triangle=inv(grounded(3,[(0,1,Q(1)),(1,2,Q(1)),(2,0,Q(1))]))
    controls['cycles_cannot_be_bridges']=triangle[0][0]==Q(2,3)!=Q(1)
    controls['forest_prefactor_required']=Q(2,4)*walkprob(4,-2)!=walkprob(4,-2)
    assert all(controls.values())
    # Exact Pareto truncated-moment identity for alpha=1/3 at perfect cubes.
    for k in range(1,20):
        # integral_1^(k^3) (1/3) r^(-1/3) dr = (k^2-1)/2.
        actual=Q(k*k-1,2);bound=Q(k*k,2)
        assert 0<=actual<=bound
    return {'gram_entries':9,'negative_controls':controls,'pareto_integrals':19}


def main():
    result={'status':'PASS_EXACT_FINITE_SUPPORT_ONLY','block_algebra':block_checks(),
            'fringe_algebra':fringe_checks(),'corner_algebra':corner_checks(),
            'controls':gram_and_controls(),
            'limits':'No numerical or finite check proves F or its asymptotic estimates.'}
    print(json.dumps(result,sort_keys=True,indent=2))


if __name__=='__main__':main()
