"""Independent finite exact checks. Read-only; no author diagnostic imports.

The universal claims are proved in the report, not by these tests.
"""
from fractions import Fraction as F
from itertools import product, combinations_with_replacement, permutations
import json, math, random

COUNT = 0
def check(v):
    global COUNT
    COUNT += 1
    assert v, COUNT

def mm(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def tr(a): return sum(a[i][i] for i in range(len(a)))
def norm(a): return sum(x*x for row in a for x in row)
def sub(a,b): return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def slices(t):
    n=len(t)
    return [[[t[i][j][r] for j in range(n)] for i in range(n)] for r in range(n)]
def gram_b(t):
    n=len(t)
    return [[sum(t[i][a][b]*t[j][a][b] for a,b in product(range(n),repeat=2)) for j in range(n)] for i in range(n)]
def maps(t):
    n=len(t); ix=list(product(range(n),repeat=2))
    p=[[sum(t[i][j][r]*t[k][l][r] for r in range(n)) for k,l in ix] for i,j in ix]
    ph=[[sum(t[i][k][r]*t[j][l][r] for r in range(n)) for k,l in ix] for i,j in ix]
    return p,ph
def comm_energy(t):
    a=slices(t)
    return sum(norm(sub(mm(x,y),mm(y,x))) for x in a for y in a)

def general_suite():
    rng=random.Random(650061)
    cases=0
    for n in range(1,6):
      for case in range(7):
        t=[[[F(0) for k in range(n)] for j in range(n)] for i in range(n)]
        for abc in combinations_with_replacement(range(n),3):
            z=F(rng.randint(-5,5),rng.randint(1,7))
            for i,j,k in set(permutations(abc)): t[i][j][k]=z
        b=gram_b(t);a=slices(t);p,ph=maps(t)
        b2=[[sum(mm(z,z)[i][j] for z in a) for j in range(n)] for i in range(n)]
        for i,j in product(range(n),repeat=2):check(b[i][j]==b2[i][j])
        check(norm(p)==norm(b));check(norm(ph)==norm(b))
        check(norm(sub(p,ph))==comm_energy(t))
        # Partial transpose of the bipartite operator P is Phi composed with transpose.
        for i,j,k,l in product(range(n),repeat=4):
            check(p[i*n+l][k*n+j]==ph[i*n+j][l*n+k])
        beta=sum((b[i][j]-int(i==j))**2 for i,j in product(range(n),repeat=2))
        off=sum(t[i][j][r]**2 for i,j,r in product(range(n),repeat=3) if i!=j)
        mixed=sum(t[i][j][r]**2 for i,j,r in product(range(n),repeat=3) if not i==j==r)
        dist=mixed+sum((abs(t[i][i][i])-1)**2 for i in range(n))
        deph=[[F(int(i==j==k==l)) for k,l in product(range(n),repeat=2)] for i,j in product(range(n),repeat=2)]
        pd=norm(sub(p,deph))
        check(pd==beta+2*off);check(2*mixed<=3*off)
        check(dist<=beta+3*mixed);check(4*dist<=9*pd)
        for i in range(n):
            z=abs(t[i][i][i]);h=b[i][i]-z*z
            check(h>=0);check((z-1)**2<=(b[i][i]-1)**2+2*h)
        cases+=1
    return cases

def simplex_suite():
    cases=[]
    for n in range(3,8):
        m=n-1;g=F(n,n-2)
        q=[[F(i==j)-F(1,n) for j in range(n)] for i in range(n)]
        t=[[[sum(q[a][i]*q[a][j]*q[a][k] for a in range(n)) for k in range(n)] for j in range(n)] for i in range(n)]
        for i,j,k in product(range(n),repeat=3):
            check(t[i][j][k]==F(i==j==k)-F(int(i==j)+int(i==k)+int(j==k),n)+F(2,n*n))
        b=gram_b(t);p0,ph0=maps(t)
        p=[[g*x for x in row] for row in p0];ph=[[g*x for x in row] for row in ph0]
        for i,j in product(range(n),repeat=2): check(g*b[i][j]==q[i][j])
        for k in range(n):check(sum(t[i][i][k] for i in range(n))==0)
        check(tr(p)==m);check(norm(p)==m)
        check(g*g*comm_energy(t)==F(2*m,m-1))
        # Full superoperator formula, with ambient compression paid on both slots.
        for i,j,k,l in product(range(n),repeat=4):
            r=i*n+j;c=k*n+l
            check(ph[r][c]-p[r][c]==F(1,m-1)*(q[i][j]*q[k][l]-q[i][k]*q[j][l]))
            # Spectrum of P^Gamma via mutually orthogonal scalar/P/symmetric/skew sectors.
            scalar=q[i][j]*q[k][l]/m
            sym=(q[i][k]*q[j][l]+q[i][l]*q[j][k])/2
            skew=(q[i][k]*q[j][l]-q[i][l]*q[j][k])/2
            remain=sym-scalar-p[r][c]
            spectral=scalar+F(m-2,m-1)*p[r][c]-remain/F(m-1)+skew/F(m-1)
            check(p[i*n+l][k*n+j]==spectral)
        neg_rank=F(m*(m+1),2)-1-m
        check(neg_rank==F((m-2)*(m+1),2))
        check(neg_rank>=0)
        # Ambient Frobenius isometry lets all projected coordinate directions be summed.
        aa=slices(t)
        for i,j in product(range(n),repeat=2):
            comm=sub(mm(aa[i],aa[j]),mm(aa[j],aa[i]))
            for k,l in product(range(n),repeat=2):
                check(g*comm[k][l]==-F(1,m-1)*(q[k][i]*q[l][j]-q[k][j]*q[l][i]))
        cases.append({'m':m,'E':str(F(2*m,m-1)),'negative_partial_transpose_trace_over_m':str(neg_rank/F(m*(m-1)))})
    return cases

def greedy_suite():
    rows=[]
    for m in [2,3,4,8,16,32,64,128,256,512]:
        r=F(m+1,m-1);energy=F(2*m,m-1)
        scale=F(1);charge=F(0);mixed=F(0);totalnorm=F(0)
        for d in range(m,1,-1):
            expected=r*F(d-1,d+1);check(scale==expected)
            c2=scale*F(d-1,d);h2=scale/F(d)
            a=scale**2/F(d-1)
            check(c2+h2==scale)
            check(c2>=F(1,6));check(F(1,3)<=scale<=1)
            # B after restriction is scalar (scale-2 lambda^2) on d-1 dimensions.
            next_scale=scale-2*scale/F(d*(d-1))
            check(next_scale==scale*F((d-2)*(d+1),d*(d-1)))
            if d>2:check(next_scale==r*F(d-2,d))
            else:check(next_scale==0)
            charge+=a;mixed+=3*h2;totalnorm+=c2+3*h2;scale=next_scale
        check(totalnorm==m)
        harmonic=sum(F(1,d) for d in range(2,m+1))
        check(charge>=harmonic/F(3))
        check(mixed>=harmonic)
        rows.append({'m':m,'adaptive_charge_over_initial_E':str(charge/energy),'mixed_loss':str(mixed)})
    return rows

def floating_suite():
    rows=[]
    for m in [2,3,4,8,16,64,256,1024,4096]:
        n=m+1;s=math.sqrt(n/(n-2));a=(1/math.sqrt(n)-1)/m;b=-1/math.sqrt(n)
        coef=s*(1+3*a+3*a*a+m*a*a*a+b**3)
        upper=2*m*(1-coef);lower=2/(1+math.sqrt(1-1/m))
        r=(m+1)/(m-1)
        mixed=sum(3*r*(d-1)/(d*(d+1)) for d in range(2,m+1))
        diag=1+sum((1-math.sqrt(r)*(d-1)/math.sqrt(d*(d+1)))**2 for d in range(2,m+1))
        rows.append({'m':m,'analytic_all_orbit_lower_evaluated':lower,'explicit_householder_upper_evaluated':upper,'greedy_cost_evaluated':mixed+diag,'E_over_m':2/(m-1),'status':'floating evaluation of proved formulas; not orbit optimization or interval certification'})
    return rows

def exact_orientation_suite():
    """Rational Householder bases independently check the global construction.

    Use n equal to a square so a,b are rational. Check the unscaled compressed
    cubic directly in ambient coordinates; its normalization factor squared is
    rational, but do not assert that the factor itself is rational.
    """
    rows=[]
    for root in [2,3,4]:
        n=root*root;m=n-1;g=F(n,n-2)
        a=(F(1,root)-1)/m;b=-F(1,root)
        u=[[F(j==i)+a if j<m else b for j in range(n)] for i in range(m)]
        for v in u:check(sum(v)==0)
        for i,j in product(range(m),repeat=2):
            check(sum(x*y for x,y in zip(u[i],u[j]))==int(i==j))
        rawdiag=1+3*a+3*a*a+m*a**3+b**3
        for v in u:check(sum(x**3 for x in v)==rawdiag)
        cost=F(0);snorm=F(0);cross=F(0)
        for i,j,k in product(range(n),repeat=3):
            t=F(i==j==k)-F(int(i==j)+int(i==k)+int(j==k),n)+F(2,n*n)
            d=sum(v[i]*v[j]*v[k] for v in u)
            cost+=(t-d)**2;snorm+=t*t;cross+=t*d
        check(snorm==F(m)/g);check(cross==m*rawdiag)
        check(cost==F(m)/g+m-2*m*rawdiag)
        check(cost<=16) # Proposition 6.1, supplied codimension-one projection.
        rows.append({'m':m,'unscaled_compressed_cubic_cost':str(cost),
                     'raw_diagonal_coefficient':str(rawdiag)})
    return rows

def run():
    result={'general_symmetric_cases':general_suite(),'exact_simplex_cases':simplex_suite(),'exact_greedy_cases':greedy_suite(),'exact_orientation_cases':exact_orientation_suite(),'floating_records':floating_suite()}
    result['exact_assertions']=COUNT
    result['scope']='Finite evidence only; universal arguments and non-nomination are in I65.'
    return result

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
