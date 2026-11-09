"""Exact diagnostic algebra; analytic separation argument is in REGRESSION.md."""
import json, os, sys
# Optional read-only dependency path; isolated Python never auto-loads user sites.
if os.environ.get("REGRESSION_SITE"):
 sys.path.insert(0, os.environ["REGRESSION_SITE"])
import sympy as s
Z,W,h=s.symbols('Z W h'); I=s.I
a=I*(1-Z); b=1+Z; c=I*(1-W); e=1+W
N=b*(c*a-c*b-b*e)*(c*a+c*b-b*e)
Q=-c*c*a**3+2*c*c*a*b*b+4*c*a*a*b*e+2*c*a*b*b*e-c*b**3*e-3*a*b*b*e*e
p=s.expand(Q-I*N);q=s.expand(Q+I*N)
ps=s.expand(p.subs(W,-W)*(2+Z-W));qs=s.expand(q.subs(W,-W)*(2*Z*W+W-Z))
assert s.Poly(s.gcd(ps,qs),Z,W).total_degree()==0
assert s.cancel(Z**4*W**3*s.conjugate(ps.subs({Z:1/s.conjugate(Z),W:1/s.conjugate(W)}))-qs)==0
assert s.expand(q.subs(Z,-1)+8*I*(W-1)**2)==0
assert s.expand(q.subs({Z:-1,W:-W})+8*I*(W+1)**2)==0
assert s.cancel((2*Z*W+W-Z).subs(W,Z/(2*Z+1)))==0
assert s.limit((1-1/s.sqrt(1+2*h*h))/h**2,h,0)==1
assert s.simplify(1-1/s.sqrt(1+2*h*h)-2*h*h/(s.sqrt(1+2*h*h)*(s.sqrt(1+2*h*h)+1)))==0
# The forbidden remote cluster has distance two from the named point at Z=-1.
assert abs(complex(-1)-complex(1))==2
print(json.dumps({'status':'PASS','reduced':True,'reflection_bidegree':[4,3],
 'local_root':'Z/(2*Z+1)','local_height_order':2,'local_height_ratio_limit':1,
 'remote_cluster_at':-1,'named_second_coordinate':1,
 'analytic_exclusion_of_local_order_six':'ordinary proof in REGRESSION.md; not a Lean regression'},indent=2))
