#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Exact finite support only; does not prove the global target H."""
import sys
sys.dont_write_bytecode = True
import json
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
from random import Random
from explore import prism, join, hcs, pm, rank, edgeset
from generate_probe import embed_prism, expand, conn3
P = Path(__file__).resolve().parent

def affine_rank(cs):
    return rank([[x-y for x,y in zip(c,cs[0])] for c in cs[1:]]) if cs else -1

def graph_ok(n,e):
    assert e == edgeset(e)
    assert all(0 <= u < v < n for u,v in e)
    adj=[[] for _ in range(n)]
    for u,v in e: adj[u].append(v);adj[v].append(u)
    assert all(len(a)==3 for a in adj)
    color={0:0};todo=[0]
    while todo:
        u=todo.pop()
        for v in adj[u]:
            if v not in color:color[v]=1-color[u];todo.append(v)
            assert color[v]!=color[u]
    assert len(color)==n and conn3(n,e)
    assert rank([[int(v in z) for z in e] for v in range(n)])==n-1
    return adj

def sphere_faces(n,e,fs):
    assert n-len(e)+len(fs)==2
    occ={z:[] for z in e};link=[{} for _ in range(n)]
    for k,f in enumerate(fs):
        assert len(set(f))==len(f) and len(f)%2==0
        for j,u in enumerate(f):
            v=f[(j+1)%len(f)];z=tuple(sorted((u,v)))
            occ[z].append((k,1 if u<v else -1))
            a,b=f[j-1],v
            link[u].setdefault(a,[]).append(b);link[u].setdefault(b,[]).append(a)
    assert all(len(a)==2 for a in occ.values())
    # Orientable closed surface: assign opposite directions to the two sides.
    adj=[[] for _ in fs]
    for (a,sa),(b,sb) in occ.values():
        adj[a].append((b,-sa*sb));adj[b].append((a,-sa*sb))
    signs={0:1};q=[0]
    while q:
        a=q.pop()
        for b,s in adj[a]:
            if b not in signs:signs[b]=signs[a]*s;q.append(b)
            assert signs[b]==signs[a]*s
    assert len(signs)==len(fs)
    for dic in link:
        assert len(dic)==3 and all(len(x)==2 for x in dic.values())
        seen={min(dic)};q=list(seen)
        while q:
            for z in dic[q.pop()]:
                if z not in seen:seen.add(z);q.append(z)
        assert seen==set(dic)

def hc_valid(n,e,c):
    if len(c)!=len(e) or any(x not in (0,1) for x in c): return False
    adj=[[] for _ in range(n)]
    for (u,v),x in zip(e,c):
        if x:adj[u].append(v);adj[v].append(u)
    if not all(len(a)==2 for a in adj):return False
    seen={0};q=[0]
    while q:
        for v in adj[q.pop()]:
            if v not in seen:seen.add(v);q.append(v)
    return len(seen)==n

def dfs_hcs(n,e):
    adj=[[] for _ in range(n)];idx={z:i for i,z in enumerate(e)};out=set()
    for u,v in e:adj[u].append(v);adj[v].append(u)
    def go(path,seen):
        u=path[-1]
        if len(path)==n:
            if 0 in adj[u] and path[1]<u:
                c=[0]*len(e)
                for a,b in zip(path,path[1:]+[0]):c[idx[tuple(sorted((a,b)))]]=1
                out.add(tuple(c))
            return
        for v in adj[u]:
            if v not in seen:go(path+[v],seen|{v})
    go([0],{0});return out

def paths3(n,e):
    adj=[[] for _ in range(n)];idx={frozenset(z):i for i,z in enumerate(e)};ps=set()
    for u,v in e:adj[u].append(v);adj[v].append(u)
    for a in range(n):
        for b in adj[a]:
            for c in adj[b]:
                if c==a:continue
                for d in adj[c]:
                    if d not in (a,b):ps.add(tuple(sorted(idx[frozenset(z)] for z in [(a,b),(b,c),(c,d)])))
    return ps

def prism_basis(m,e):
    ix={z:i for i,z in enumerate(e)};out=[]
    def edge(u,v):return ix[tuple(sorted((u,v))) ]
    for i in range(m):
        c=[0]*len(e)
        for j in range(m):
            if j!=i:c[edge(j,(j+1)%m)]=c[edge(m+j,m+(j+1)%m)]=1
        c[edge(i,m+i)]=c[edge((i+1)%m,m+(i+1)%m)]=1;out.append(c)
    for s in [0,1]:
        c=[0]*len(e)
        for j in range(m):
            c[edge(j,m+j)]=1
            c[edge(j,(j+1)%m) if j%2==s else edge(m+j,m+(j+1)%m)]=1
        out.append(c)
    return out

def main():
    for m in range(4,22,2):
        n,e=prism(m);cs=hcs(n,e);bs=prism_basis(m,e)
        graph_ok(n,e);assert all(hc_valid(n,e,c) for c in bs)
        assert set(map(tuple,cs))==set(map(tuple,bs))
        assert len(cs)==m+2 and affine_rank(bs)==m+1
        if m<=8:assert set(map(tuple,cs))==dfs_hcs(n,e)
    print('P: 9 even prisms, exact explicit bases/counts/ranks; 3 DFS cross-checks PASS')
    for a,b in [(4,4),(6,4),(8,4),(10,4),(6,6)]:
        n,e=join(prism(a),prism(b));graph_ok(n,e);cs=hcs(n,e)
        assert all(hc_valid(n,e,c) for c in cs)
        assert affine_rank(cs)==n//2+1
        # Reconstruct all compatible pairs explicitly (all 3 omission classes).
        n1,e1=prism(a);n2,e2=prism(b);c1=hcs(n1,e1);c2=hcs(n2,e2)
        ns1=sorted(v if u==0 else u for u,v in e1 if 0 in (u,v))
        ns2=sorted(v if u==0 else u for u,v in e2 if 0 in (u,v))
        ee={tuple(z):k for k,z in enumerate(e)};got=set();classes=[0,0,0]
        for z in c1:
            st1=[z[e1.index(tuple(sorted((0,u))))] for u in ns1]
            for t in c2:
                st2=[t[e2.index(tuple(sorted((0,u))))] for u in ns2]
                if st1!=st2:continue
                classes[st1.index(0)]+=1;v=[0]*len(e)
                for (u,w),x in zip(e1,z):
                    if 0 not in (u,w):v[ee[(u-1,w-1)]]=x
                for (u,w),x in zip(e2,t):
                    if 0 not in (u,w):v[ee[(u+n1-2,w+n1-2)]]=x
                for j,(u,w) in enumerate(zip(ns1,ns2)):
                    v[ee[tuple(sorted((u-1,w+n1-2)))]]=st1[j]
                got.add(tuple(v))
        assert all(classes) and got==set(map(tuple,cs))
    print('S: 5 splice fiber-product correspondences and full exact affine ranks PASS')
    x=json.loads((P/'local-witness.json').read_text());n=x['n'];e=[tuple(z) for z in x['edges']]
    graph_ok(n,e);cs=hcs(n,e);assert len(cs)==12 and set(map(tuple,cs))==dfs_hcs(n,e)
    ss=[cs[k] for k in x['chosen']]
    assert x['supports']==[[i for i,v in enumerate(c) if v] for c in ss]
    ps=paths3(n,e);assert len(ps)==84
    assert all(any(all(c[j] for j in p) for c in ss) for p in ps)
    assert all(any(not c[j] for c in ss) for j in range(len(e)))
    assert affine_rank(ss)==x['rank']==6 and affine_rank(cs)==8
    cert=x['rank_minor'];diff=[[a-b for a,b in zip(c,ss[0])] for c in ss[1:]]
    mat=[[Q(diff[i][j]) for j in cert['columns']] for i in cert['difference_rows']]
    determinant=Q(1)
    for j in range(len(mat)):
        k=next(k for k in range(j,len(mat)) if mat[k][j])
        if k!=j:mat[k],mat[j]=mat[j],mat[k];determinant=-determinant
        q=mat[j][j];determinant*=q;mat[j]=[v/q for v in mat[j]]
        for k in range(j+1,len(mat)):
            q=mat[k][j];mat[k]=[u-q*v for u,v in zip(mat[k],mat[j])]
    assert determinant==Q(cert['determinant'])!=0 and len(mat)==6
    squares=set();edge_ids={frozenset(z):i for i,z in enumerate(e)}
    from itertools import permutations
    for vs in combinations(range(n),4):
        for per in permutations(vs[1:]):
            vs4=(vs[0],)+per
            es4=[frozenset((vs4[i],vs4[(i+1)%4])) for i in range(4)]
            if all(z in edge_ids for z in es4):squares.add(tuple(sorted(edge_ids[z] for z in es4)))
    assert len(squares)==6
    assert all(len({tuple(c[j] for j in sq) for c in ss})==6 for sq in squares)
    assert min(sum(c[j] for c in ss) for j in range(len(e)))>=4
    w=list(map(Q,x['weight']));cost=[sum(a*b for a,b in zip(w,c)) for c in cs]
    assert list(map(str,cost))==x['all_costs']
    assert {cost[k] for k in x['chosen']}=={Q(-2)} and set(cost)=={-3,-2,-1}
    print('W: 14 vertices; 12 HCs; 8 witnesses cover 84 P4s/all 6 square traces; >=4 per edge; ranks 6 < 8/minor checked; costs {-3,-2,-1} PASS')
    for m in [4,6,10]:
        g=embed_prism(m);n,e,fs=g;cs=hcs(n,e)
        i=e.index((0,m));j=e.index((1,m+1));ss=[c for c in cs if c[i] or c[j]]
        assert len(ss)==5 and affine_rank(ss)==4
        h=expand(g,2,1,3);n,e,fs=h;graph_ok(n,e);sphere_faces(n,e,fs);cc=hcs(n,e)
        assert affine_rank(cc)==m+3
        assert len(cc)=={4:8,6:14,10:26}[m]
    print('L: direct lifts retain just 5 cycles/rank 4 at m=4,6,10; expanded ranks 7,9,13 PASS')
    # The same fixed probes as the recorded exploration, with stronger graph/embedding checks.
    rng=Random(6126);g=embed_prism(4);num=0;mx=0
    for k in range(160):
        if k%4==0:g=embed_prism(rng.choice([4,6,8]))
        opts=[(f,i,j) for f,h in enumerate(g[2]) for i,j in combinations(range(len(h)),2) if (j-i)%2==0]
        h=expand(g,*rng.choice(opts));n,e,fs=h
        if not conn3(n,e):continue
        graph_ok(n,e);sphere_faces(n,e,fs);g=h;cc=hcs(n,e)
        assert cc and all(hc_valid(n,e,c) for c in cc)
        assert affine_rank(cc)==n//2+1
        num+=1;mx=max(mx,n)
    assert num==160
    print(f'G: {num} seeded probes, possible isomorphic duplicates, max vertices {mx}; hypotheses and exact ranks PASS')
    controls=0
    assert affine_rank(ss)!=m+1;controls+=1
    n,e=prism(4);bad=[int(u//4==v//4) for u,v in e]
    assert all(sum(x for z,x in zip(e,bad) if v in z)==2 for v in range(n)) and not hc_valid(n,e,bad);controls+=1
    witness_all=hcs(x['n'],[tuple(z) for z in x['edges']])
    witness_selected=[witness_all[k] for k in x['chosen']]
    wrong=list(w);wrong[0]+=1
    assert len({sum(a*b for a,b in zip(wrong,c)) for c in witness_selected})>1;controls+=1
    damaged=[c[:] for c in witness_selected];damaged[0][0]^=1
    assert not hc_valid(x['n'],[tuple(z) for z in x['edges']],damaged[0]);controls+=1
    print(f'C: {controls} deliberate mathematical controls rejected PASS')
    print('PASS_FINITE_SUPPORT_ONLY_GLOBAL_H_UNRESOLVED')

if __name__=='__main__':main()
