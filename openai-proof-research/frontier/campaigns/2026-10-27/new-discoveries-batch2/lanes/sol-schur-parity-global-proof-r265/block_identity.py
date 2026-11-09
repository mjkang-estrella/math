from pathlib import Path
import sympy as S,json
L=Path(__file__).resolve().parent;k=S.Symbol('k',integer=True,positive=True)
def ramp(p,kmin=1):
 p=S.expand(p);a=p.coeff(k);b=p.subs(k,0)
 assert p==a*k+b and a.is_integer and b.is_integer
 if a>=0 and p.subs(k,kmin)>=0:return p
 if a<=0 and p.subs(k,kmin)<=0:return S.Integer(0)
 raise ValueError(('unresolved ramp',p,kmin))
def triangular(p):
 r=ramp(p);return S.expand(r*(r+1)/2)
def half_floor(m):
 m=S.sympify(m);a=S.expand(m).coeff(k);b=m.subs(k,0);assert a%2==0
 return a*k/2+S.floor(b/2),int(b%2)
def H(m,t):
 q,par=half_floor(m)
 return S.expand(2*(triangular(q+t)-triangular(t-1))-ramp(t)-(1-par)*ramp(q+t))
def block(a,b,c,d,e,f):
 terms=[(b-e+1,1),(a-e,-1),(b-f,-1),(a-f-1,1)]
 return S.expand(sum(s*(H(d,t)-H(c-1,t)) for t,s in terms))
def total(blocks):
 return S.expand(sum(block(a,b,c,d,e,f) for a,b,col in blocks for c,d,col2 in blocks for e,f,col3 in blocks if col==col2==col3))
att=[]
for r in range(12):
 n=12*k+r;s=2*k+(r+3)//6;t=6*k+(r+1)//2;u=10*k+(5*r+3)//6
 p=total([(1,s,0),(s+1,t,1),(t+1,u,0),(u+1,n,1)])
 target=S.expand((n*n-r*r)/6+(r*r+5)//6)
 assert S.expand(p-target)==0
 att.append(dict(n=str(n),count=str(p),range='integer k>=1'))
blow=[]
# word blocks, with stretch h=2k+e: k>=1 suffices for both parities;
# h=1 is separately exact-enumerated, and is outside source n>=12.
word=[0,1,0,1,1,0,0,1,0,1,1]
for e in (0,1):
 h=2*k+e;blocks=[(i*h+1,(i+1)*h,col) for i,col in enumerate(word)]
 p=total(blocks);assert S.expand(p-(85*h*h-5*e)/4)==0
 blow.append(dict(stretch=str(h),count=str(p),range='integer k>=1'))
out={'method':'Exact positive-part interval convolution; no polynomial interpolation','attainment':att,'exceptional_word_blowup':blow}
(L/'block-identity.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
