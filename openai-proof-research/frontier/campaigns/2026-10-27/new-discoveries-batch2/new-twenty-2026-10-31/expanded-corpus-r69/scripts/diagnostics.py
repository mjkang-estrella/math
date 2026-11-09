import os,resource,time,json,pathlib,itertools,random,sys
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
P=pathlib.Path(__file__).resolve().parents[1];start=time.time();rng=random.Random(6901)
def spectral():
 import numpy as np
 # Points of PG(2,3) represented by normalized nonzero triples.
 pts=[x for x in itertools.product(range(3),repeat=3) if any(x) and next(v for v in x if v)==1];B=np.array([[sum(a*b for a,b in zip(x,y))%3==0 for y in pts] for x in pts],dtype=int)
 A=np.block([[np.zeros((13,13),int),B],[B.T,np.zeros((13,13),int)]]);assert np.all(B@B.T==3*np.eye(13,dtype=int)+np.ones((13,13),int))
 cases=[]
 for k in range(1,401):
  C=A.copy()
  for _ in range(1+(k%12)):
   edges=list(zip(*np.where(np.triu(C,1))))
   for trial in range(50):
    (a,b),(c,d)=rng.sample(edges,2)
    if rng.randrange(2):c,d=d,c
    if len({a,b,c,d})==4 and not C[a,c] and not C[b,d]:
     C[a,b]=C[b,a]=C[c,d]=C[d,c]=0;C[a,c]=C[c,a]=C[b,d]=C[d,b]=1;break
  ev=np.linalg.eigvalsh(C);cases.append({'case':k,'median_abs':float(max(abs(ev[12]),abs(ev[13]))),'edges':[list(map(int,e)) for e in zip(*np.where(np.triu(C,1)))]})
 # Component padding and edge deletion are separate mechanisms.
 dels=[]
 for a,b in list(zip(*np.where(np.triu(A,1)))):
  C=A.copy();C[a,b]=C[b,a]=0;ev=np.linalg.eigvalsh(C);dels.append(float(max(abs(ev[12]),abs(ev[13]))))
 return {'mechanisms':['degree-preserving two-switch perturbations of PG(2,3)','single-edge deletions'], 'baseline_spectrum':np.linalg.eigvalsh(A).tolist(),'switch_cases':cases,'single_edge_deletion_medians':dels,'counterexample_cases':[x for x in cases if x['median_abs']>2**.5+1e-8],'warning':'Floating spectra diagnostic only; switches can return the exceptional graph; no exact certificate or nonisomorphism claim.'}
def bch():
 out=[]
 for m,f in [(3,11),(4,19),(5,37),(6,67),(7,131),(8,285)]:
  n=2**m-1
  def mul(a,b):
   v=0
   while b:
    if b&1:v^=a
    b>>=1;a<<=1
    if a&(1<<m):a^=f
   return v
  powers=[1]
  for _ in range(n-1):powers.append(mul(powers[-1],2))
  assert len(set(powers))==n and mul(powers[-1],2)==1
  for t in range(1,m):
   roots=set()
   for i in range(1,2**t+1):
    j=i%n
    while j not in roots:roots.add(j);j=2*j%n
   g=[1]
   for j in sorted(roots):
    h=[0]*(len(g)+1)
    for a,c in enumerate(g):h[a]^=mul(c,powers[j]);h[a+1]^=c
    g=h
   assert set(g)<={0,1};gb=sum(c<<i for i,c in enumerate(g));dim=n-len(g)+1;db=(2**m-2)//(2**(m-t)-1)+1
   r={'m':m,'t':t,'length':n,'generator_hex':hex(gb),'dimension':dim,'Bose_formula':db}
   if dim<=20:
    best=n+1;word=0;prev=0;wit=None
    for i in range(1,1<<dim):
     gray=i^(i>>1);flip=gray^prev;word^=gb<<(flip.bit_length()-1);prev=gray;w=word.bit_count()
     if w<best:best=w;wit=word
    r.update(exact_enumeration_minimum=best,witness_hex=hex(wit),codewords_checked=(1<<dim)-1)
   else:r['outcome']='skipped dimension cap'
   out.append(r)
 return {'cases':out,'warning':'Exact Python cyclic-code model, not Lean certified; generator-to-source defining-set bridge not formalized.'}
def odd():
 import numpy as np
 from scipy.optimize import milp,Bounds,LinearConstraint
 cases=[]
 def solve(n,edges,label):
  E=len(edges);nv=E*3+n*6;mat=[];lb=[];ub=[]
  for e in range(E):
   row=np.zeros(nv);row[e*3:e*3+3]=1;mat.append(row);lb.append(1);ub.append(1)
  for v in range(n):
   inc=[e for e,(a,b) in enumerate(edges) if v in (a,b)];d=len(inc)
   for c in range(3):
    z=3*E+6*v+2*c;y=z+1;row=np.zeros(nv)
    for e in inc:row[3*e+c]=1
    row[z]=-2;row[y]=-1;mat.append(row);lb.append(0);ub.append(0)
    row=np.zeros(nv)
    for e in inc:row[3*e+c]=1
    row[y]=-d;mat.append(row);lb.append(-np.inf);ub.append(0)
  bounds_hi=np.ones(nv)
  for v in range(n):
   for c in range(3):bounds_hi[3*E+6*v+2*c]=sum(v in e for e in edges)//2
  res=milp(np.zeros(nv),integrality=np.ones(nv),bounds=Bounds(np.zeros(nv),bounds_hi),constraints=LinearConstraint(np.array(mat),lb,ub),options={'time_limit':2,'threads':1})
  r={'label':label,'n':n,'edges':edges,'status':int(res.status),'message':res.message}
  if res.x is not None:
   colors=[int(np.argmax(res.x[3*e:3*e+3])) for e in range(E)];counts=[[sum(colors[e]==c and v in ed for e,ed in enumerate(edges)) for c in range(3)] for v in range(n)];valid=all(d==0 or d%2==1 for row in counts for d in row);r.update(colors=colors,counts=counts,exact_integer_validation=valid)
  cases.append(r)
 for n in [5,7,9,11,13]:
  for shifts in [(1,2),(1,3),(2,3)]:
   if max(shifts)*2>=n:continue
   edges=sorted({tuple(sorted((v,(v+s)%n))) for v in range(n) for s in shifts});solve(n,edges,f'circulant-{shifts}')
 # Source Section 5 obstruction to extending the four-connected proof: 27 vertices.
 edges=[]
 for i in range(4):
  off=6*i
  edges += [(off+a,off+b) for a in range(6) for b in range(a+1,6) if a//2!=b//2 and (a,b)!=(0,2)]
  edges +=[(24,off+a) for a in range(6)]+[(25,off),(26,off+2)]
 edges +=[(25,26)];solve(27,edges,'source-section5-four-octahedra')
 return {'cases':cases,'warning':'MILP failure/timeouts do not certify noncolorability. Explicit returned colorings are rechecked with integer counts. Connectivity not formally certified.'}
fun={'spectral':spectral,'bch':bch,'odd':odd}[sys.argv[1]];data=fun();data['wall_seconds']=time.time()-start;data['peak_RSS_KiB']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss;data['affinity']=sorted(os.sched_getaffinity(0));data['CPU_limit_seconds']=120;data['address_space_limit_bytes']=6*1024**3;(P/'outputs'/f'{sys.argv[1]}-diagnostic.json').write_text(json.dumps(data,indent=2)+'\n');print(sys.argv[1],data['wall_seconds']);print(json.dumps(data)[:700] if sys.argv[1]!='bch' else json.dumps(data))
