import itertools,pathlib,json,hashlib,time,runpy
L=pathlib.Path(__file__).resolve().parents[1]
ns=runpy.run_path(str(L/'scripts/mathcheck.py'));span=ns['span'];autos=ns['autos']
def subs(k):
 for piv in itertools.combinations(range(5),k):
  free=[(i,j) for i,p in enumerate(piv) for j in range(p+1,5) if j not in piv]
  for mask in range(1<<len(free)):
   rows=[1<<p for p in piv]
   for t,(i,j) in enumerate(free):
    if (mask>>t)&1:rows[i]^=1<<j
   yield rows,span(rows)
def v(x):return sum(3<<(2*i) for i in range(5) if x>>i&1)
def u(x):return sum(1<<(2*i) for i in range(5) if x>>i&1)
spaces={k:list(subs(k)) for k in range(6)};print('subspace counts',{k:len(x) for k,x in spaces.items()},flush=True)
allcodes=set();counts={}
for a in range(3):
 count=0
 for ar,A in spaces[a]:
  for br,B in spaces[5-a]:
   if not A<=B:continue
   reps=sorted({min(x^b for b in B) for x in range(32)})
   for fs in itertools.product(reps,repeat=a):
    rows=[v(b) for b in br]+[u(x)^v(f) for x,f in zip(ar,fs)]
    C=tuple(sorted(span(rows)));assert len(C)==32;allcodes.add(C);count+=1
 counts[a]=count
assert len(allcodes)==18291
print('all invariant dimension5 codes',counts,len(allcodes),flush=True)
# Explicit full centralizer action, not just a sample of generators.
tables=[]
for p in itertools.permutations(range(5)):
 for mask in range(32):
  images=[2*p[i//2]+((i%2)^((mask>>(i//2))&1)) for i in range(10)]
  table=[0]*1024
  for x in range(1,1024):
   bit=x&-x;table[x]=table[x^bit]^(1<<images[bit.bit_length()-1])
  tables.append(table)
remaining=set(allcodes);results=[]
while remaining:
 C=min(remaining);orbit={tuple(sorted(t[w] for w in C)) for t in tables};assert orbit<=allcodes
 found,nodes=autos(set(C),10,3)
 assert len(found)>=3, ('counterexample',C,found)
 extra=next(p for p in found if p!=tuple(range(10)) and p!=tuple(i^1 for i in range(10)))
 # Check the alleged extra automorphism directly against all words.
 assert {sum(((w>>i)&1)<<extra[i] for i in range(10)) for w in C}==set(C)
 results.append({'representative':C,'orbit_size':len(orbit),'extra_automorphism':extra,'nodes':nodes})
 remaining-=orbit
 print('orbit',len(results),'size',len(orbit),'remaining',len(remaining),flush=True)
r={'invariant_dimension5_count':len(allcodes),'by_rank_T':counts,'centralizer_order':len(tables),'orbits':results,'coverage_sha256':hashlib.sha256(repr(sorted(allcodes)).encode()).hexdigest(),'counterexamples':0,'minimal_length':12,'qualification':'length <=8 and dimension/codimension <=4 excluded by source Corollaries 4.5-4.8; dimension5 length10 exhaustively checked'}
(L/'independent-10.json').write_text(json.dumps(r,indent=2)+'\n')
