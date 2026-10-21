"""Finite Q(sqrt(5)) angular cone certificate. Independent of numerical sampling."""
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations,product
import runpy,json
ROOT=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r160')
# Load the polynomial definitions without executing the diagnostic main/output.
s=(ROOT/'affine_moments.py').read_text().split('out={}\nfor l,h in H.items():')[0]
ns={};exec(compile(s,'affine_moments definitions','exec'),ns)
add,mul,power,der,sphere,T=[ns[k] for k in ['add','mul','power','der','sphere','T']]
class Q:
    def __init__(self,a=0,b=0):
        if isinstance(a,Q):self.a,self.b=a.a,a.b
        else:self.a,self.b=F(a),F(b)
    def __add__(self,x):x=Q(x);return Q(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self):return Q(-self.a,-self.b)
    def __sub__(self,x):return self+-Q(x)
    def __rsub__(self,x):return Q(x)+-self
    def __mul__(self,x):x=Q(x);return Q(self.a*x.a+5*self.b*x.b,self.a*x.b+self.b*x.a)
    __rmul__=__mul__
    def __truediv__(self,x):
        x=Q(x);d=x.a*x.a-5*x.b*x.b
        if not d:raise ZeroDivisionError
        return self*Q(x.a/d,-x.b/d)
    def __bool__(self):return bool(self.a or self.b)
    def __eq__(self,x):x=Q(x);return self.a==x.a and self.b==x.b
    def __hash__(self):return hash((self.a,self.b))
    def __repr__(self):return str(self.a)+' + ('+str(self.b)+')sqrt5'
def mons(l):return [(a,b,l-a-b) for a in range(l+1) for b in range(l-a+1)]
def rref(M):
    M=[list(row) for row in M];piv=[];r=0
    for c in range(len(M[0])):
        k=next((k for k in range(r,len(M)) if M[k][c]),None)
        if k is None:continue
        M[r],M[k]=M[k],M[r];d=M[r][c];M[r]=[x/d for x in M[r]]
        for j in range(len(M)):
            if j!=r and M[j][c]:
                a=M[j][c];M[j]=[x-a*y for x,y in zip(M[j],M[r])]
        piv.append(c);r+=1
        if r==len(M):break
    return M,piv
basis=[]
for l in [2,3,4]:
    mm=mons(l);small=mons(l-2);rows=[]
    for k in small:
        row=[]
        for m in mm:
            row.append(sum(F(m[j]*(m[j]-1)) for j in range(3) if m[j]>=2 and tuple(m[i]-(2 if i==j else 0) for i in range(3))==k))
        rows.append(row)
    mat,piv=rref(rows)
    for c in range(len(mm)):
        if c in piv:continue
        a={mm[c]:F(1)}
        for row,p in zip(mat,piv):
            if row[c]:a[mm[p]]=-row[c]
        assert not add(*(der(der(a,i),i) for i in range(3)))
        basis.append((l,a))
assert len(basis)==21
# Vertices of the regular 600-cell; antipodal quaternions give the same rotation.
phi=Q(F(1,2),F(1,2));invphi=phi-Q(1);quats=[]
for i in range(4):
    for sign in [-1,1]:quats.append(tuple(Q(sign if j==i else 0) for j in range(4)))
quats += [tuple(Q(F(a,2)) for a in signs) for signs in product([-1,1],repeat=4)]
for signs in product([-1,1],repeat=3):
    q=(Q(0),Q(F(signs[0],2)),phi*F(signs[1],2),invphi*F(signs[2],2))
    for p in permutations(range(4)):
        if sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2==0:quats.append(tuple(q[i] for i in p))
assert len(set(quats))==120
rots=[]
for w,x,y,z in quats:
    assert w*w+x*x+y*y+z*z==1
    R=((1-2*(y*y+z*z),2*(x*y-z*w),2*(x*z+y*w)),(2*(x*y+z*w),1-2*(x*x+z*z),2*(y*z-x*w)),(2*(x*z-y*w),2*(y*z+x*w),1-2*(x*x+y*y)))
    if R not in rots:rots.append(R)
assert len(rots)==60
moment={}
for l in [2,3,4]:
 for m in mons(l):
    h={m:F(1)};moment[m]=sphere(add(*(mul(mul(T[i],T[j]),der(der(h,i),j)) for i in range(3) for j in range(3))))
columns=[]
for R in rots:
    linear=[{tuple(int(i==j) for i in range(3)):R[k][j] for j in range(3)} for k in range(3)]
    powers=[[power(p,n) for n in range(5)] for p in linear]
    col=[]
    for l,h in basis:
        rotated={}
        for m,c in h.items():
            pp=mul(mul(powers[0][m[0]],powers[1][m[1]]),powers[2][m[2]])
            rotated=add(rotated,{k:v*c for k,v in pp.items()})
        col.append(sum((c*moment[m] for m,c in rotated.items()),Q(0)))
    columns.append(col)
rows=[[col[i] for col in columns] for i in range(21)]
zero_sum=all(sum(row,Q(0))==0 for row in rows)
_,piv=rref(rows);rank=len(piv)
assert zero_sum
# Full row rank and the strictly positive uniform kernel vector imply positive cone = R^21.
assert rank==21,(rank,piv)
def enc(q):q=Q(q);return [str(q.a),str(q.b)]
out={'field':'Q(sqrt(5))','basis':[{'degree':l,'coefficients':{str(k):str(v) for k,v in h.items()}} for l,h in basis],'rotations':[[[enc(v) for v in row] for row in R] for R in rots],'columns':[[enc(v) for v in c] for c in columns],'rank':rank,'pivot_columns_zero_based':piv,'uniform_column_sum_zero':zero_sum,'meaning':'Angular limiting cone only. Not a full instruction-routing or force construction.'}
(ROOT/'notes/shell-cone-certificate.json').write_text(json.dumps(out,indent=2))
print('exact rotations',len(rots),'harmonic dimension',len(basis),'rank',rank,'uniform positive relation',zero_sum,'pivots',piv)
