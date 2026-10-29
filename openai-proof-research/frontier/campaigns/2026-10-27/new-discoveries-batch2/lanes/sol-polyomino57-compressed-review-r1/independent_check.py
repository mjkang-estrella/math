"""Independent certificate audit; does not execute or import supplied programs.
Python exact set geometry; signed int16 inequality arithmetic; complement-pair merges.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1';os.environ['MKL_NUM_THREADS']='1'
import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(160,165));signal.alarm(175)
import pathlib,json,gzip,hashlib,itertools,time,collections
import numpy as np
HERE=pathlib.Path(__file__).resolve().parent
SRC=HERE/'input-copy'
START=time.monotonic()

def geometry(a,b,e):
    # Integer (u,v), no Cartesian scanning box and no supplied geometry data.
    vertices=[(u,v) for u in range(a+1) for v in range(e,e+b+1) if (u+v)%2==0]
    centers={(s,t) for s in range(a-5,6) for t in range(e+b-5,e+6) if (s+t)%2==0}
    constraints={frozenset(i for i,(u,v) in enumerate(vertices) if (u-s,v-t) in {(4,0),(-4,0),(0,4),(0,-4)}) for s,t in centers}
    for coord,level in [(0,0),(0,a),(1,e),(1,e+b)]:
        constraints.add(frozenset(i for i,p in enumerate(vertices) if p[coord]==level))
    minimal=sorted([tuple(sorted(g)) for g in constraints if all(not h<g for h in constraints)])
    # Exact deletion implication, including empty-set domination.
    assert all(any(set(h)<=g for h in minimal) for g in constraints)
    assert all(frozenset(g) in constraints for g in minimal)
    edges=[(i,j) for i,p in enumerate(vertices) for j,q in enumerate(vertices[:i]) if abs(p[0]-q[0])==abs(p[1]-q[1])==1]
    return vertices,centers,minimal,edges

def connected(p,edges):
    if not p:return False
    seen={min(p)}
    while True:
        more=seen|{j for i,j in edges if i in seen and j in p}|{i for i,j in edges if j in seen and i in p}
        if more==seen:return seen==p
        seen=more

def table_check(d,gs,edges):
    n,N=d.shape;k=len(gs)
    assert N==1<<k and np.all((1<=d)&(d<=12))
    assert d.dtype==np.int16
    # Compute common intersections per mask, not submasks of vertex cover.
    intersections=[set(range(n))]
    bases=0
    for m in range(1,N):
        bit=m&-m
        common=intersections[m^bit]&set(gs[bit.bit_length()-1]);intersections.append(common)
        for v in common:assert int(d[v,m])==1;bases+=1
    for i,j in edges:assert np.all(np.abs(d[i,1:]-d[j,1:])<=1)
    merge_count=0
    # Enumerate disjoint pairs from complement of A, independent of union masks.
    for a in range(1,N):
        complement=(N-1)^a;b=complement;parts=[]
        while b:
            if b>a:parts.append(b)
            b=(b-1)&complement
        if parts:
            bs=np.asarray(parts,dtype=np.int32)
            assert np.all(d[:,a|bs] <= d[:,a,None]+d[:,bs]-1)
            merge_count+=len(parts)*n
    assert np.all(d[:,-1]==12)
    return {'base_checks':bases,'edge_checks':len(edges)*(N-1),'merge_checks':merge_count,'min':int(d.min()),'max':int(d.max())}

# All 110 nominal span/parity boxes and the stated parity maps.
normalization=[]
for a in range(1,11):
 for b in range(1,a+1):
  for e in range(2):
    V,S,G,E=geometry(a,b,e)
    target_e=e
    if e and a%2:
        image={(a-u,v-1) for u,v in V};target_e=0;mapname='a-reflection'
    elif e and b%2:
        image={(u,b+1-v) for u,v in V};target_e=0;mapname='b-reflection'
    else:image=set(V);mapname='identity'
    assert image==set(geometry(a,b,target_e)[0])
    # Check adjacency is preserved by each actual affine formula.
    f=(lambda u,v:(a-u,v-1)) if mapname=='a-reflection' else ((lambda u,v:(u,b+1-v)) if mapname=='b-reflection' else (lambda u,v:(u,v)))
    assert all(abs(f(*V[i])[0]-f(*V[j])[0])==abs(f(*V[i])[1]-f(*V[j])[1])==1 for i,j in E)
    normalization.append([a,b,e,target_e,mapname])

rows=[];payload_names=set();entries=compressed=0
metadata=json.loads((SRC/'group-domains.json').read_text())
for a,b,e,te,name in normalization:
    if e!=te:continue
    V,S,G,E=geometry(a,b,e);n=len(V);k=len(G)
    old=next(r for r in metadata if (r['a'],r['b'],r['e'])==(a,b,e))
    assert old['V']==list(map(list,V)) and old['G']==list(map(list,G)) and set(map(tuple,old['S']))==S
    assert {(min(i,j),max(i,j)) for i,adj in enumerate(old['adj']) for j in adj}=={(j,i) for i,j in E}
    rec={'domain':[a,b,e],'vertices':n,'groups':k,'centers':len(S)}
    if not G[0]:rec['kind']='empty-group'
    else:
        forced={g[0] for g in G if len(g)==1}
        if len(forced)>=8:
            trials=conn=0;misses=collections.Counter()
            if len(forced)<=11:
                available=sorted(set(range(n))-forced)
                for extra_count in range(12-len(forced)):
                    for extra in itertools.combinations(available,extra_count):
                        p=forced|set(extra);trials+=1
                        if connected(p,E):
                            conn+=1
                            absent=[j for j,g in enumerate(G) if p.isdisjoint(g)]
                            assert absent;misses.update(absent)
            rec.update(kind='forced',forced=len(forced),checks=trials,connected=conn,missed_groups=dict(misses))
        else:
            name=f'steiner-{a}-{b}-{e}.bin.gz';payload_names.add(name)
            expected=n*(1<<k)
            with gzip.open(SRC/name,'rb') as f:raw=f.read(expected+1)
            assert len(raw)==expected
            # File is mask-major, vertex-minor, with both lexicographic orders
            # reconstructed above. Transpose; widen BEFORE all arithmetic.
            d=np.frombuffer(raw,dtype='u1').reshape((1<<k,n)).T.astype(np.int16)
            checks=table_check(d,G,E)
            rec.update(kind='potential',entries=expected,raw_sha256=hashlib.sha256(raw).hexdigest(),checks=checks)
            entries+=expected;compressed+=(SRC/name).stat().st_size
    rows.append(rec)
assert len(rows)==70
assert payload_names==set(json.loads((SRC/'certificate-files.json').read_text()))
assert collections.Counter(r['kind'] for r in rows)=={'empty-group':35,'forced':4,'potential':31}
assert sum(r.get('checks',0) for r in rows if r['kind']=='forced')==596
assert entries==1874144 and compressed==238227

# Cartesian falsifier and every possible center: bounding by one occupied point
# is exhaustive because any good center is within Manhattan distance 5 of it.
P={(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-2),(0,-2),(1,-2),(1,-1),(1,0),(1,1),(2,1)}
H={(2,2),(2,-2),(-2,2),(-2,-2)}
C={(x,y) for x in range(-5,6) for y in range(-5,6) if abs(x)+abs(y)<=5}-H
assert len(C)==57
cart_edges=lambda p:[(i,j) for i,x in enumerate(p) for j,y in enumerate(p[:i]) if abs(x[0]-y[0])+abs(x[1]-y[1])==1]
assert connected(set(range(57)),cart_edges(sorted(C)))
# D4 invariance of C under generators suffices.
assert {(-y,x) for x,y in C}==C and {(x,-y) for x,y in C}==C
assert len(P)==11 and connected(set(range(11)),cart_edges(sorted(P)))
anchor=min(P);possible={(anchor[0]+x,anchor[1]+y) for x in range(-5,6) for y in range(-5,6) if abs(x)+abs(y)<=5}
good=sorted(c for c in possible if all((x-c[0],y-c[1]) in C for x,y in P))
assert good==[(1,-1)]
radius=min(max(abs(x-c[0])+abs(y-c[1]) for x,y in P) for c in possible)
assert radius==4
five={(0,0),(1,0),(-1,0),(0,1),(0,-1)}
collisions={str(c):sorted((x,y) for x,y in P if (x-c[0],y-c[1]) in H) for c in five}
assert all(collisions.values())
Q={(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-2),(0,-2),(1,-2)}
assert all(any((x-cx,y-cy) in H for x,y in Q) for cx,cy in five)

out={'status':'PASS','seconds':time.monotonic()-START,'normalizations':normalization,'domains':rows,'entries':entries,'compressed_bytes':compressed,'empty_center_domains':[r['domain'] for r in rows if r['centers']==0],'falsifier':{'P':sorted(P),'good_centers':good,'radius':radius,'five_collisions':collisions},'resources':{'AS':536870912,'cpu':[160,165],'alarm':175,'BLAS_threads':1}}
(HERE/'independent-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['normalizations','domains']},indent=2))
