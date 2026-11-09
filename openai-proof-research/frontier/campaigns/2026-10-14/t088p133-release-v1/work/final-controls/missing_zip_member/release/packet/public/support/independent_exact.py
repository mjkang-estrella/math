# Independent final-manuscript review: symbolic partial-fraction construction.
# Copyright 2026 Myeongjin Kang. MIT.
from pathlib import Path
import sympy as s,json,re,hashlib
O=Path(__file__).resolve().parents[1];P=O/'work/extracted/packet/public'
rows=json.loads((P/'support/certificate-witness.json').read_text());results=[]
for row in rows:
 k,l,z=row['pattern'];x=s.symbols('x1:'+str(k+1));y=s.symbols('y1:'+str(l+1));vs=x+y
 u=[sum(x[i:]) for i in range(k)];v=[sum(y[j:]) for j in range(l)]
 den=s.prod(a+b for a in u for b in v)
 # Direct product residues; cancellation uses exact rational polynomials.
 np=0;nP=0
 for i,a in enumerate(u):
  ai=s.prod(a/(a-c) for j,c in enumerate(u) if i!=j)*s.prod(a/(a+b) for b in v)
  np+=ai;nP+=ai*a
 np=s.Poly(s.cancel(np*den),*vs);nP=s.Poly(s.cancel(nP*den),*vs)
 # Sorted entries are -v1,...,-vl, zeros, uk,...,u1.
 ordered=[-a for a in v]+[s.Integer(0)]*z+u[::-1]
 D=s.expand(sum((2*i-3)*a for i,a in enumerate(ordered)))
 T=s.Poly(5*nP.as_expr()*den-D*np.as_expr()**2,*vs)
 pp={'Np':np,'NP':nP,'Den':s.Poly(den,*vs),'D':s.Poly(D,*vs),'T':T}
 for key,pol in pp.items():
  want={tuple(e):s.Rational(c) for e,c in row[key]};assert pol.as_dict()==want,(row['pattern'],key)
 # Parse every printed sparse coefficient directly from the TeX appendix.
 text=(P/'witness-tables.tex').read_text();piece=text.split('\\subsection{Pattern ('+','.join(map(str,row['pattern']))+')}')[1].split('\\subsection')[0]
 table={}
 for e,c in re.findall(r'\$\(([0-9,]+)\)\$&(\d+)',piece):
  ee=tuple(map(int,e.split(',')));assert ee not in table;table[ee]=s.Integer(c)
 assert table==T.as_dict();assert all(a>0 for a in table.values())
 ep=[0]*(k+l);ep[k-1]=2*k*l+1;assert table[tuple(ep)]==k*(k+1)
 results.append({'pattern':[k,l,z],'terms':len(table),'all_five_polynomials':'MATCH','table_coefficients':'MATCH','pure_endpoint':[ep,k*(k+1)]})
assert sum(q['terms'] for q in results)==248
# Universal polynomial slack and both formal decompositions.
a,b,A,B,p,d=s.symbols('alpha beta A B p d');q=1-p
F=p*A*b+q*B*a-d*a*b;G=A*B-d*(p*a*B+q*b*A)
assert s.expand((a+A)*(b+B)-(1+d)*(p*a*(b+B)+q*b*(a+A))-F-G)==0
assert s.expand((F-(p*b*(A-2*d*p)+q*a*(B-2*d*q)+d*(2*p-a)**2)).subs(b,2-a))==0
assert s.expand((G-(a*B*(A-2*d*p)+b*A*(B-2*d*q))/2).subs(b,2-a))==0
result={'patterns':results,'total_terms':248,'method':'independent SymPy rational residue cancellation; direct printed-TeX parsing','universal_slack_and_residual_identities':'EXACT_ZERO','sympy_version':s.__version__}
(O/'evidence/independent-exact.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
