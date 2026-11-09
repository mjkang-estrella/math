from pathlib import Path
import sys,json,re,collections,time,resource,contextlib,io,runpy,os,math,itertools,hashlib
from fractions import Fraction
L=Path(__file__).resolve().parent;F=L/'frozen'
os.environ['CERT_VERIFY_ONLY']='1'
with contextlib.redirect_stdout(io.StringIO()):g=runpy.run_path(str(F/'check.py'))
N=g['N'];used=g['used'];sorts=g['sorts'];P=g['P'];h=g['h']
assert all(all(j<i for j in x) and isinstance(N[x[0]],str) for i,x in enumerate(N) if isinstance(x,tuple))
assert all(sorts[N[i][1]]=='Int' for i in used if isinstance(N[i],tuple) and h(i) in ['<','>','<=','>='])
# All actual arithmetic equality constraints have Int operands, never Bool.
eqs=[]
for i in P:
 if h(i)!='th-lemma':continue
 todo=[N[i][-1]]+[N[j][-1] for j in N[i][1:-1]]
 seen=set()
 while todo:
  j=todo.pop()
  if j in seen:continue
  seen.add(j);x=N[j]
  if not isinstance(x,tuple):continue
  if h(j)=='=':assert sorts[x[1]]=='Int';eqs.append(j)
  elif h(j) in ['and','or','not']:todo.extend(x[1:])
# Exercise the actual lexical parser in isolation, without its initial file writes.
s=(F/'inspect.py').read_text();s=s[s.index('def parse(s):'):s.index('start=time.monotonic()')]
e=dict(sys=sys,re=re);exec(s,e)
def expand(t):
 i=e['resolve'](e['parse'](t)[0],e['Env']())
 def tree(i):
  x=e['nodes'][i];return x if isinstance(x,str) else tuple(tree(j) for j in x)
 return tree(i)
assert expand('(let ((x m)) (let ((x H) (y x)) (+ x y)))')==('+','H','m')
assert expand('(let ((x m)) (let ((x (+ x 1))) (+ x m)))')==('+',('+','m','1'),'m')
assert expand('(let ((x m)) (let ((x H) (y x)) (+ x y)))')!=expand('(let ((x m)) (let ((x H)) (let ((y x)) (+ x y))))')
# Independently evaluate gcd/floor and exact strict complement on negative
# constants and arbitrary positive rational clearing. Tests supplement the proof.
rows=0
for a,b,c,den in itertools.product(range(-4,5),range(-3,4),range(-7,8),range(1,4)):
 d={'x':Fraction(a,den),'y':Fraction(b,den),None:Fraction(c,den)}
 coeff,constant=g['row'](d)
 for x,y in [(-3,2),(0,0),(1,-2),(4,3)]:
  actual=a*x+b*y+c>=0
  reduced=sum(v*{'x':x,'y':y}[k] for k,v in coeff)+constant>=0
  assert actual==reduced
 # geform complement orientation after integral clearing
 g['B'][:]=[None,None];g['bc'].clear();g['memo'].clear();g['atoms'].clear()
 u=g['geform'](d);v=g['geform']({'x':-a,'y':-b,None:-c-1})
 assert g['app']('and',u,v)==0 and g['app']('or',u,v)==1
 rows+=1
# Independent original finite-sum evaluation vs the exact 64-clamp expression,
# with indexed masks (including empty mask and repeated entries).
cases=0
for m in range(1,8):
 for aa in itertools.combinations_with_replacement(range(m),4):
  for H in range(1,m+1):
   direct=clamps=0
   for mask in range(16):
    s=sum(aa[j] for j in range(4) if mask>>j&1);sign=(-1)**(4-mask.bit_count())
    direct+=sign*sum((j+s)//m for j in range(H))
    clamps+=sign*sum(max(0,min(H,s+H-level*m)) for level in range(1,5))
   assert direct==clamps
   cases+=1
files={n:{'lines':len((F/n).read_text().splitlines()),'bytes':(F/n).stat().st_size,'sha256':hashlib.sha256((F/n).read_bytes()).hexdigest()} for n in ['check.py','inspect.py','mapping.py','final_verify.py']}
out={'status':'PASS','topological_nodes':len(N),'all_heads_literal_atoms':True,'actual_arithmetic_equalities_Int':len(set(eqs)),'lexical_tests':3,'normalization_cases':rows,'finite_mapping_cases':cases,'finite_checks_are_not_universal_proof':True,'trusted_code_sizes':files}
(L/'critical-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
