import sympy as s,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];t,u,L=s.symbols('t u L');z,w=s.symbols('z w')
A=s.Matrix([[-z,1,1,1,0],[1,-w,0,1,0],[1,0,-w,0,1],[1,1,0,-z,1],[0,0,1,1,-z]])
N=s.factor(A.minor_submatrix(0,0).det());Q=s.factor(A.det());F=s.expand((N-L*Q).subs({z:1/t,w:t*u})*t)
print('N=',N,'Q=',Q,'F(t,u,L)=',F)
# F has simple roots u=1,3 at t=0 for nonzero L.
allrows={}
for u0 in [1,3]:
 cs=s.symbols('c1:7');U=u0+sum(cs[i-1]*t**i for i in range(1,7));pol=s.Poly(s.expand(F.subs(u,U)),t);sol={}
 for i,c in enumerate(cs):sol[c]=s.factor(s.solve(pol.nth(i+1).subs(sol),c)[0])
 print('root',u0,'w coefficients',sol);allrows[str(u0)]={str(c):str(v) for c,v in sol.items()}
 R=s.expand(F.subs(u,U.subs(sol)));assert all(s.simplify(R.coeff(t,i))==0 for i in range(7))
(D/'outputs/contact-exact.json').write_text(json.dumps({'edges':[[0,1],[0,2],[0,3],[1,3],[2,4],[3,4]],'z_vertices':[0,3,4],'w_vertices':[1,2],'root':0,'numerator':str(N),'denominator':str(Q),'scaled_level_equation':str(F),'branch_coefficients':allrows},indent=2))
