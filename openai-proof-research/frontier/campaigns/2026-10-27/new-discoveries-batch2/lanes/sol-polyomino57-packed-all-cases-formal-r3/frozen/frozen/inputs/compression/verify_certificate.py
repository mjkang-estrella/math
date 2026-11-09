"""Check lower-bound potentials, not the DP algorithm or animal enumeration.
Each value L(M,v) is <= the size of every connected vertex set containing v
which meets group mask M. Base, edge and disjoint-merge inequalities suffice.
"""
import os,resource,signal,pathlib,json,gzip,hashlib,time,itertools
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(160,165));signal.alarm(175)
import numpy as np
L=pathlib.Path(__file__).parent;receipts=[];start=time.monotonic();total=compressed=0
for a in range(1,11):
 for b in range(1,a+1):
  for e in range(2):
   if e and (a%2 or b%2):continue
   # Build cells in x,y, then order by signed-diagonal coordinates.
   cells=sorted([(x,y) for x in range(-10,12) for y in range(-10,12) if 0<=x+y<=a and e<=x-y<=e+b],key=lambda p:(sum(p),p[0]-p[1]));n=len(cells)
   centers=[(x,y) for x in range(-10,12) for y in range(-10,12) if a-5<=x+y<=5 and e+b-5<=x-y<=e+5]
   holes={(2,2),(2,-2),(-2,2),(-2,-2)}
   groups={sum(1<<i for i,(x,y) in enumerate(cells) if (x-cx,y-cy) in holes) for cx,cy in centers}
   groups.update(sum(1<<i for i,(x,y) in enumerate(cells) if f(x,y)==bound) for f,bound in [(lambda x,y:x+y,0),(lambda x,y:x+y,a),(lambda x,y:x-y,e),(lambda x,y:x-y,e+b)])
   # Drop only constraints implied by a smaller constraint.
   gs=[g for g in groups if not any(h!=g and h&g==h for h in groups)]
   gs.sort(key=lambda g:[i for i in range(n) if g>>i&1]);k=len(gs)
   rec=dict(a=a,b=b,e=e,vertices=n,groups=k)
   if 0 in gs:rec['verified']='empty-constraint';receipts.append(rec);continue
   forced={i for g in gs if g.bit_count()==1 for i in range(n) if g>>i&1}
   if len(forced)>=8:
    trials=0;connected_count=0;left=set(range(n))-forced
    for extra in range(12-len(forced)):
     for add in itertools.combinations(sorted(left),extra):
      trials+=1;P=forced|set(add);seen={next(iter(P))};queue=list(seen)
      for v in queue:
       x,y=cells[v]
       for w in P-seen:
        z,t=cells[w]
        if abs(x-z)+abs(y-t)==1:seen.add(w);queue.append(w)
      if seen==P:
       connected_count+=1;mask=sum(1<<v for v in P)
       assert any(mask&g==0 for g in gs)
    rec.update(verified='forced-cell-small-check',forced_cells=len(forced),supersets_checked=trials,connected_supersets=connected_count);receipts.append(rec);continue
   file=L/f'steiner-{a}-{b}-{e}.bin.gz';raw=gzip.decompress(file.read_bytes());assert len(raw)==(1<<k)*n
   D=np.frombuffer(raw,dtype=np.uint8).reshape((1<<k,n));assert np.all((1<=D)&(D<=12));N=1<<k
   # Every one-vertex witness gives a base inequality, including all subsets.
   for v in range(n):
    cover=sum(1<<i for i,g in enumerate(gs) if g>>v&1);m=cover
    while m:assert D[m,v]<=1;m=(m-1)&cover
   # Moving the distinguished vertex across an edge costs at most one.
   edges=[(v,w) for v,(x,y) in enumerate(cells) for w,(z,t) in enumerate(cells) if abs(x-z)+abs(y-t)==1]
   for v,w in edges:assert np.all(D[1:,v]<=D[1:,w]+1)
   merges=0
   for m in range(1,N):
    parts=[];s=(m-1)&m
    while s:
     if s<(m^s):parts.append(s)
     s=(s-1)&m
    if parts:
     ix=np.array(parts,dtype=np.int32)
     assert np.all(D[m]<=D[ix]+D[ix^m]-1)
     merges+=len(parts)*n
   assert np.all(D[N-1]>=12)
   total+=len(raw);compressed+=file.stat().st_size
   rec.update(verified='potential-inequalities',entries=len(raw),merge_inequalities=merges,sha256=hashlib.sha256(file.read_bytes()).hexdigest());receipts.append(rec)
# Explicit shortcut falsifier: connected, eleven cells, radius exactly four.
P={(-2,-2),(-2,-1),(-2,0),(-2,1),(-1,-2),(0,-2),(1,-2),(1,-1),(1,0),(1,1),(2,1)}
seen={next(iter(P))}
while True:
 nxt=seen|{q for q in P if any(abs(q[0]-p[0])+abs(q[1]-p[1])==1 for p in seen)}
 if nxt==seen:break
 seen=nxt
assert seen==P and len(P)==11 and max(abs(x)+abs(y) for x,y in P)==4
assert max(x+y for x,y in P)-min(x+y for x,y in P)==7
five=[(0,0),(1,0),(-1,0),(0,1),(0,-1)]
assert all(any((x-cx,y-cy) in holes for x,y in P) for cx,cy in five)
valid=[(cx,cy) for cx in range(-10,11) for cy in range(-10,11) if all(abs(x-cx)+abs(y-cy)<=5 and (x-cx,y-cy) not in holes for x,y in P)]
assert valid
out=dict(status='PASS',domains=len(receipts),dp_domains=sum(r['verified']=='potential-inequalities' for r in receipts),entries=total,compressed_certificate_bytes=compressed,full_original_certificate_bytes=10880385,byte_compression_ratio=10880385/compressed,domain_reduction_ratio=135268/len(receipts),seconds=time.monotonic()-start,eleven_cell_five_shift_falsifier=sorted(P),valid_centers_for_falsifier=valid,receipts=receipts)
(L/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='receipts'},indent=2))
