import sympy as s,json,pathlib,functools
L=pathlib.Path(__file__).resolve().parent
u,v,t=s.symbols('u v t',real=True)
# Direct log-series algebra, no candidate modules/results imported.
phi=sum(s.exp(s.I*t*z).series(t,0,7).removeO() for z in (-u,u-v,v))/3
z=s.expand(phi-1)
log=sum((-1)**(j+1)*z**j/s.Integer(j) for j in range(1,4))
# z starts at t^2; three powers suffice to t^6.
B={k:s.expand(log).coeff(t,k).expand() for k in range(2,7)}
P2=s.expand(B[4]+B[3]**2/2)
P4=s.expand(B[6]+B[3]*B[5]+B[4]**2/2+B[3]**2*B[4]/2+B[3]**4/24)
# Gaussian integration by parts in u, then the one-dimensional fp recurrence.
# Values normalized by sqrt(3)/pi. M(0,k)=J_k/(4 sqrt(pi)).
@functools.lru_cache(None)
def J(k):
 if k%2:return s.S(0)
 if k==-2:return -s.S(1)
 if k==0:return s.S(2)
 assert k>=2
 return 2*(k-1)*J(k-2)
@functools.lru_cache(None)
def mom(p,q):
 if p<0:return mom(q,p)
 if p==0:return J(q)/4
 return s.Rational(3,2)*(p-1)*mom(p-2,q) + s.Rational(1,2)*mom(p-1,q+1) if p>1 else mom(0,q+1)/2
def integ(F):
 ans=0;terms=[]
 for term in s.Add.make_args(s.expand(F)):
  powers=term.as_powers_dict();p=int(powers.get(u,0));q=int(powers.get(v,0));c=term/u**p/v**q
  assert p>=-2 and q>=-2 and max(p,q)>=0
  a=s.simplify(c*mom(p,q));ans+=a;terms.append([p,q,str(c),str(a)])
 return s.simplify(ans),terms
pieces=[4*P4/u**2/v**2,(1/u**2+1/v**2)*P2/3,(v**2/u**2+u**2/v**2)/60,s.Rational(1,36)]
vals=[integ(f) for f in pieces]
out={'method':'direct formal log through degree6; Gaussian IBP recurrence; no candidate imports','B':{str(k):str(x) for k,x in B.items()},'P2':str(P2),'P4':str(P4),'normalized_pieces':[str(a) for a,_ in vals],'monomials':[b for _,b in vals],'sum':str(sum(a for a,_ in vals))}
assert out['sum']=='-4/81'
assert [str(a) for a,_ in vals]==['-11/405','-1/36','-1/120','1/72']
(L/'independent-check.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='monomials'},indent=2))
