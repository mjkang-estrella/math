import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import runpy,pathlib,contextlib,json,resource,itertools
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
# Import definitions without running the enumeration driver.
L=pathlib.Path(__file__).resolve().parents[1];ns={};exec((L/'scripts/snake.py').read_text().split('for n in range(0,13):')[0],ns);hp=ns['hp']
import sympy as sp
x=sp.Symbol('x');seen=set()
for n in range(0,17):
 count=0;new=0;bad=[]
 for w in itertools.product(range(2),repeat=n):
  if n and w[0]:continue
  h=tuple(hp(w));count+=1
  if h in seen:continue
  seen.add(h);new+=1;p=sp.Poly.from_list(list(h[::-1]),x)
  if p.count_roots(-sp.oo,0)!=p.degree():bad.append({'word':w,'h':h})
 print(json.dumps({'letters':n,'complement_orbit_representatives':count,'new_distinct_polynomials_Sturm_checked':new,'total_distinct':len(seen),'bad':bad}),flush=True)
