import resource,os,time,json,pathlib
resource.setrlimit(resource.RLIMIT_CPU,(45,45));resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,)*2);os.sched_setaffinity(0,{0,1})
import sympy as s
x=s.symbols('x');start=time.process_time();out=[]
for n in [3,5,15,21,33,39,51,57,105,165,195,231,255,285]:
 if time.process_time()-start>30:break
 p=s.Poly(s.cyclotomic_poly(n,x),x);q=p.diff();cnt=q.count_roots(-s.oo,s.oo);g=s.gcd(q,q.diff());r={'n':n,'degree':p.degree(),'real_critical_points':int(cnt),'derivative_squarefree':g.degree()==0,'cpu':time.process_time()-start};out.append(r);print(r,flush=True)
pathlib.Path(__file__).resolve().parent.parent.joinpath('cyclotomic-diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
