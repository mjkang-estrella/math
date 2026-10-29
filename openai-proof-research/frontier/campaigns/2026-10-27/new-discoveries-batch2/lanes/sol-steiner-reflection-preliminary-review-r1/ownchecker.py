import os,resource,signal,time,json,itertools,math
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']: os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(45)
import sympy as S
from fractions import Fraction as Q
from pathlib import Path
start=time.monotonic();s=S.Symbol('s');n=30
# Orbit enumeration: 0=center; 1=distinguished fixed leaf (leaf equation only).
# Anonymous leaves introduced in first-occurrence order; each pattern carries
# falling-factorial multiplicity, rather than enumerating actual triples.
def patterns(base,slots=3):
 def rec(t,r):
  if len(t)==slots: yield t,r;return
  for j in range(base+r):yield from rec(t+(j,),r)
  yield from rec(t+(base+r,),r+1)
 yield from rec((),0)
def dist(t):
 # Minimal star subtree has one edge per distinct leaf, except singleton leaf.
 a=set(t);return 0 if len(a)==1 else len(a-{0})
def orbital(fixed):
 base=1 if fixed==0 else 2;pool=29 if fixed==0 else 28
 total=0;count=0;mass=0
 for (j,k,h),r in patterns(base):
  mult=math.prod(range(pool-r+1,pool+1));mass+=mult;count+=1
  x=lambda v:s+29 if v==0 else -1
  y=lambda v:s/15-x(v)
  total+=mult*dist((fixed,j,k,h))*x(j)*x(k)*y(h)
 assert mass==30**3
 return S.expand(total),count
c,nc=orbital(0);l,nl=orbital(1)
d=2*s**3-26*s**2+32*s+30;L=86*s**3-728*s**2+894*s+810
assert S.expand(c-29*d/30)==0 and S.expand(l-L/30)==0
P=S.expand(30*c+(s+29)**3*30*l)
assert P.subs(s,5)==-85295770 and P.subs(s,8)==273617240
assert S.expand(d-(30-48*s+2*s*(s-5)*(s-8)))==0
assert (34*c-29*l).subs(s,5)==-S.Rational(14413,3)
# Direct entry check from unions of actual graph paths, including repeated indices.
def path(a,b):
 if a==b:return set()
 return {tuple(sorted((0,j))) for j in (a,b) if j!=0}
def graphdist(t):
 e=set()
 for v in t[1:]:e|=path(t[0],v)
 return len(e)
entries=[]
for t in [(0,0,0,0),(1,1,1,1),(0,1,1,1),(1,2,3,4),(1,1,2,2),(0,29,29,28),(29,28,27,26)]:
 assert graphdist(t)==dist(t)
 i,j,k,z=t
 a=sum(Q(graphdist((i,j,k,h)))*(Q(1,15)-(h==z)) for h in range(30))
 b=sum(Q(dist((i,j,k,h)))*(Q(1,15)-(h==z)) for h in range(30))
 assert a==b;entries.append({'tuple':t,'C':str(a)})
# Prove non-full-symmetry by actual entries, not by generic warning.
def C(t):
 i,j,k,z=t;return sum(Q(graphdist((i,j,k,h)))*(Q(1,15)-(h==z)) for h in range(30))
a=C((0,0,0,1));b=C((1,0,0,0));assert a!=b
# Arbitrary-vector mixed cut identity on a small actual star; full tuple sum.
N=5;vec=[[Q((i+2)*(r+1)%7-3,r+1) for i in range(N)] for r in range(4)]
direct=sum(Q(graphdist(t))*math.prod(vec[r][t[r]] for r in range(4)) for t in itertools.product(range(N),repeat=4))
cut=sum(math.prod(map(sum,vec))-math.prod(v[j] for v in vec)-math.prod(sum(v)-v[j] for v in vec) for j in range(1,N))
assert direct==cut
result={'passed':True,'method':'restricted-growth orbital triples, falling-factorial weights; symbolic coefficients, no interpolation','center_patterns':nc,'leaf_patterns':nl,'center':str(c),'leaf':str(l),'P':str(P),'P5':int(P.subs(s,5)),'P8':int(P.subs(s,8)),'quartic5':str((34*c-29*l).subs(s,5)),'nonsymmetric_entries':[str(a),str(b)],'sampled_entries':entries,'mixed_cut_N5':str(direct),'seconds':time.monotonic()-start,'maxrss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'limits':{'AS_MiB':512,'CPU_s':35,'alarm_s':45,'BLAS_threads':1},'proof_status':'diagnostics only; unconditional derivation in review.md'}
Path(__file__).with_name('ownchecker-results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
