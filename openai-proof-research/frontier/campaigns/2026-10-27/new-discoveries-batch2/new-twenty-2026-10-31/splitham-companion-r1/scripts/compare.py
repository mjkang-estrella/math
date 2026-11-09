import itertools as it,json,collections
from pathlib import Path

def graph(m,D):
    adj=[set() for _ in range(2*m)]
    for a,b in it.combinations(range(m),2):adj[a].add(b);adj[b].add(a)
    for i in range(m):
        for d in D:
            j=(i+d)%m;adj[j].add(m+i);adj[m+i].add(j)
    return adj

def audit(m,D,delete_check=False,dp=False):
    r=len(D);a=graph(m,D);bad={0:None,1:None};counts=collections.Counter()
    for v in range(2*m):
        for leaves in it.combinations(a[v],r+1):
            e=sum(y in a[x] for x,y in it.combinations(leaves,2))
            counts[min(e,2)]+=1
            if e<2 and bad[e] is None:bad[e]=[v,list(leaves)]
    checked=0;disconnect=None
    if delete_check:
        for k in range(r):
            for cut in it.combinations(range(2*m),k):
                rem=set(range(2*m))-set(cut);seen={next(iter(rem))};stack=list(seen)
                while stack:
                    v=stack.pop()
                    for w in a[v]&rem-seen:seen.add(w);stack.append(w)
                checked+=1
                if seen!=rem:disconnect=list(cut);break
            if disconnect is not None:break
    ends=None
    if dp:
        states={1:{0}}
        for size in range(1,2*m):
            nxt={}
            for mask,vs in states.items():
                for v in vs:
                    for w in a[v]:
                        if not mask>>w&1:nxt.setdefault(mask|1<<w,set()).add(w)
            states=nxt
        ends=sorted(states.get((1<<(2*m))-1,set()))
        assert all(x>=m for x in ends)
    result=dict(m=m,r=r,order=2*m,offsets=list(D),edges=sum(map(len,a))//2,forbidden_leaf_edge_histogram=dict(counts),forbidden_witnesses=bad,min_clique_neighbourhood_intersection=min(len((a[x]&a[y])&set(range(m,2*m))) for x,y in it.combinations(range(m),2)),deleted_cross_edges=m*(m-r),cut_sets_checked=checked,small_cut=disconnect,dp_endpoints_from_clique_zero=ends,meets_order_bound=2*m>=2*r+7)
    assert bad[0] is None and bad[1] is None
    assert disconnect is None
    return result
out={'complete_family':[audit(r,range(r),True,r<=5) for r in range(3,9)],'sparsifications':[audit(9,[0,1,2,3,5],True),audit(10,[0,1,2,3,6]),audit(11,[0,1,2,4,7]),audit(10,range(6),True),audit(12,range(7))]}
# Verify the literal X,Y,w union equals the balanced-join encoding.
for r in range(3,9):
    Y=set(range(r));X=set(range(r,2*r-1));w=2*r-1
    E={tuple(sorted((x,y))) for x in X for y in Y}|set(it.combinations(sorted(Y|{w}),2))
    a=graph(r,range(r));F={(x,y) for x in range(2*r) for y in a[x] if x<y}
    assert E==F
out['literal_union_identity_checked_r']=list(range(3,9))
Path('outputs/comparison.json').write_text(json.dumps(out,indent=2)+'\n')
# All passages referring to companion [12], including the paragraph continuation.
lines=Path('../splitham-review-r1/outputs/source-text.txt').read_text().splitlines()
ranges=[(64,69),(98,105),(108,116),(142,146),(167,172),(182,184),(783,786),(818,819)]
Path('outputs/target-excerpts.txt').write_text('\n\n'.join('\n'.join(f'{i}: {lines[i-1]}' for i in range(lo,hi+1)) for lo,hi in ranges)+'\n')
print('Verified complete family, literal union identity, five sparsifications; see outputs/comparison.json')
