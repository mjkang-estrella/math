from pathlib import Path
import sys,json,hashlib,re
sys.dont_write_bytecode=True
sys.path.insert(0,'/home/mj-kang/.local/lib/python3.14/site-packages')
import sympy as s
z,w,x,u,Z,W,h=s.symbols('z w x u Z W h',real=False);I=s.I
edges={(0,1),(0,2),(0,3),(1,3),(2,4),(3,4)}
M=s.zeros(5)
for a,b in edges:M[a,b]=M[b,a]=1
for a in range(5):M[a,a]=-w if a in (1,2) else -z
Q=s.expand(M.det());N=s.expand(M.minor_submatrix(0,0).det())
assert s.expand(N-(w*z-w-1)*(w*z+w-1))==0
assert s.expand(Q-(-w*w*z**3+2*w*w*z+4*w*z*z+2*w*z-w-3*z))==0
R=s.cancel(x**3*(Q-I*N).subs(z,-1/x))
F=s.cancel(R.subs(w,x*u)/x**2)
# Derive jets recursively from the actual matrix polynomial, no supplied branch jets.
jets=[]
for slope in [-1,-3]:
 jet=s.Integer(slope)
 for k in range(1,6):
  a=s.Symbol('a'); coeff=s.expand(F.subs(u,jet+a*x**k)).coeff(x,k)
  sol=s.solve(coeff,a);assert len(sol)==1
  jet+=s.expand(sol[0])*x**k
 residual=s.Poly(s.expand(F.subs(u,jet)),x)
 assert all(residual.nth(k)==0 for k in range(6))
 imcoeff=[s.im(s.expand(jet*x).coeff(x,k)) for k in range(1,7)]
 order=next(k for k,c in enumerate(imcoeff,1) if c!=0)
 jets.append({'slope':slope,'w_jet':str(s.expand(jet*x)),'imaginary_order':order,'imaginary_leading':str(imcoeff[order-1])})
assert [j['imaginary_order'] for j in jets]==[6,2]
a=I*(1-Z);b=1+Z;c=I*(1-W);e=1+W
Nc=s.cancel(b**3*e**2*N.subs({z:a/b,w:c/e}));Qc=s.cancel(b**3*e**2*Q.subs({z:a/b,w:c/e}))
p=s.expand(Qc-I*Nc);q=s.expand(Qc+I*Nc)
assert s.expand(q.subs(Z,-1)+8*I*(W-1)**2)==0
ps=s.expand(p.subs(W,-W)*(2+Z-W));qs=s.expand(q.subs(W,-W)*(2*Z*W+W-Z))
assert s.Poly(s.gcd(ps,qs),Z,W).total_degree()==0
assert s.simplify(Z**4*W**3*s.conjugate(ps.subs({Z:1/s.conjugate(Z),W:1/s.conjugate(W)}))-qs)==0
assert s.expand(q.subs({Z:-1,W:-W})+8*I*(W+1)**2)==0
v=Z/(2*Z+1)
assert s.cancel((2*Z*W+W-Z).subs(W,v))==0
# For unit Z: |2Z+1|^2=5+4 Re Z=1+2|Z+1|^2.
t=s.symbols('t',real=True)
assert s.expand((5+4*t)-(1+2*(2+2*t)))==0
hh=s.symbols('hh',positive=True)
height=1-1/s.sqrt(1+2*hh**2)
assert s.limit(height/hh**2,hh,0)==1
print(json.dumps({'matrix_numerator':str(N),'matrix_denominator':str(Q),'desingularized':str(s.expand(F)),'derived_jets':jets,'maximum_local_order':6,'diagnostic_reduced':True,'diagnostic_reflection':[4,3],'diagnostic_local_root':str(v),'diagnostic_height_ratio_limit':1,'diagnostic_local_order':2},indent=2))
