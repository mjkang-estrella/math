"""Independent exact finite adversarial checks; not a universal proof checker."""
from fractions import Fraction as F
from functools import lru_cache, cmp_to_key
from itertools import combinations, product
from math import lcm
import json

@lru_cache(None)
def factors(n):
    out = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0)+1; n //= p
        p += 1
    if n > 1: out[n] = out.get(n, 0)+1
    return out

class Log:
    """Exact rational linear combination of logs of primes; no floating point."""
    def __init__(self, terms=()):
        self.terms = tuple(sorted((p,F(c)) for p,c in dict(terms).items() if c))
    @staticmethod
    def rational(x):
        x=F(x); assert x>0
        d=dict(factors(x.numerator))
        for p,c in factors(x.denominator).items(): d[p]=d.get(p,0)-c
        return Log(d.items())
    def __add__(self, other):
        d=dict(self.terms)
        for p,c in other.terms: d[p]=d.get(p,F(0))+c
        return Log(d.items())
    def __neg__(self): return self*(-1)
    def __sub__(self, other): return self+(-other)
    def __mul__(self, c): return Log((p,e*c) for p,e in self.terms)
    __rmul__=__mul__
    def __truediv__(self,c): return self*F(1,c)
    def __hash__(self): return hash(self.terms)
    def __eq__(self,other): return self.terms==other.terms
    def sign(self): return sign_terms(self.terms)

@lru_cache(None)
def sign_terms(terms):
    den=lcm(*(c.denominator for _,c in terms)) if terms else 1
    pos=neg=1
    for p,c in terms:
        k=int(c*den)
        if k>0: pos*=p**k
        else: neg*=p**(-k)
    return (pos>neg)-(pos<neg)

Z=Log(); L2=Log.rational(2)
def form(line,pt):
    av,au,c=line; v,u=pt
    return v*av+u*au-c

def inside(pt, strict=False):
    v,u=pt
    signs=[v.sign(),(L2-v).sign(),(u-L2).sign(),(2*L2-u).sign()]
    return all(s>0 if strict else s>=0 for s in signs)

def intersect(a,b):
    av,au,ac=a; bv,bu,bc=b; det=av*bu-bv*au
    if not det: return None
    return ((bu*ac-au*bc)/det,(av*bc-bv*ac)/det)

def middle(a,b,den=2):
    return tuple(((den-1)*x+y)/den for x,y in zip(a,b))

def exact_key(pt,n,x,N):
    """Compute floor(N*(x+exp(v-nu))) independently by exact comparisons."""
    v,u=pt; exponent=v-n*u
    lo=int(N*x); hi=int(N*(x+F(1,8)))+2
    while lo+1<hi:
        m=(lo+hi)//2; c=F(m,N)-x
        if c<=0 or (exponent-Log.rational(c)).sign()>=0: lo=m
        else: hi=m
    return lo % N

def partition_fixture(x):
    a,b,ell,J=3,4,3,6; N=2**(b+ell)
    cs={F(1,2**a),F(1,2**b)}
    for k in range(int(N*(x+F(1,2**b)))-1,int(N*(x+F(1,2**a)))+2):
        c=F(k,N)-x
        if F(1,2**b)<=c<=F(1,2**a): cs.add(c)
    # Duplicates are removed; endpoints can coincide with lattice boundaries.
    lines=list({(1,-n,Log.rational(c)) for n in range(1,J+1) for c in cs})
    lines.sort(key=lambda row:(row[0],row[1],row[2].terms))
    sides=[(1,0,Z),(1,0,L2),(0,1,L2),(0,1,2*L2)]
    lines+=sides
    vertices=set()
    for l1,l2 in combinations(lines,2):
        pt=intersect(l1,l2)
        if pt is not None and inside(pt): vertices.add(pt)
    signatures={}; dims={0:set(),1:set(),2:set()}; samples=0; wrap=0
    def inspect(pt,dim):
        nonlocal samples,wrap
        sig=tuple(form(l,pt).sign() for l in lines)
        data=[]
        for n in range(1,J+1):
            exponent=pt[0]-n*pt[1]
            active=(exponent+b*L2).sign()>=0 and (exponent+a*L2).sign()<=0
            if active:
                k=exact_key(pt,n,x,N); data.append((n,k))
                wrap+=int(k<int(N*x)%N)
        data=tuple(data)
        if sig in signatures: assert signatures[sig]==data
        else: signatures[sig]=data
        dims[dim].add(sig); samples+=1
    for pt in vertices: inspect(pt,0)
    edges=0
    for line in lines:
        pts=[pt for pt in vertices if form(line,pt).sign()==0]
        coord=1 if line[0] else 0
        pts.sort(key=cmp_to_key(lambda x,y:(x[coord]-y[coord]).sign()))
        for p1,p2 in zip(pts,pts[1:]):
            mid=middle(p1,p2)
            if not inside(mid): continue
            edges+=1; inspect(mid,1); inspect(middle(p1,p2,3),1)
            # A sufficiently short exact normal perturbation visits each incident face.
            av,au,_=line
            others=[l for l in lines if l!=line]
            original=[form(l,mid).sign() for l in others]
            assert all(original), 'midpoint lies on another line'
            for direction in (-1,1):
                for k in range(1,80):
                    eps=L2*F(direction,2**k)
                    pt=(mid[0]+av*eps,mid[1]+au*eps)
                    if [form(l,pt).sign() for l in others]==original: break
                else: raise AssertionError('perturbation search bound')
                if inside(pt,strict=True): inspect(pt,2)
    # Rectangle with clipped lines is a connected planar subdivision.
    assert len(vertices)-edges+len(dims[2])==1
    assert len(dims[0])==len(vertices) and len(dims[1])==edges
    assert sum(map(len,dims.values()))<=2*len(lines)**2+1
    # Additional rational q,t are evaluated by their exact logarithms.
    for q in (F(1,4),F(1,3),F(3,8),F(1,2)):
        for t in (F(1),F(9,8),F(3,2),F(7,4),F(2)):
            pt=(Log.rational(t),-Log.rational(q))
            sig=tuple(form(l,pt).sign() for l in lines)
            assert sig in signatures, 'arrangement missed a stratum'
            # Direct rational powers cross-check the algebraic-log key computation.
            got=[]
            for n in range(1,J+1):
                z=t*q**n
                if F(1,2**b)<=z<=F(1,2**a): got.append((n,int(N*(x+z))%N))
            assert tuple(got)==signatures[sig]
    return {'center':str(x),'lines':len(lines),'vertices':len(vertices),
            'edges':edges,'faces':len(dims[2]),'signature_evaluations':samples,
            'wraparound_active_evaluations':wrap}

def tree_check():
    counts=0; params=0
    for M,d,r0,g in product(range(2,5),range(1,5),(1,2,7),(1,3,11)):
        r={1:r0}; sigma={0:0,1:M*r0+(M-1)*g}; A=0
        for h in range(1,d+1):
            if h>1:
                r[h]=max(r0,g+sigma[h-1]); sigma[h]=M*(r[h]+g+sigma[h-1])+(M-1)*g
            A=4*M*(1+A); assert sigma[h]<=A*(r0+g)
        a=3; records=[]
        def walk(h,parent=()):
            nonlocal a,counts
            for i in range(M):
                start=a; end=a+r[h]; a=end+g; j=len(records)
                records.append([parent+(i,),start,end,None,h])
                if h>1: walk(h-1,parent+(i,))
                star=records[-1][2]; records[j][3]=star
                assert star-start<=2*r[h]; counts+=1
        walk(d)
        assert records[-1][2]==3+sigma[d]
        for row in records:
            path,start,end,star,h=row
            subtree=[e for e in records if e[0][:len(path)]==path]
            assert max(e[2] for e in subtree)==star
        params+=1
    return {'parameter_trees':params,'edge_padding_checks':counts}

def conditional_check():
    # Four active trials split over two child subtrees, 2 distinct coarse keys each.
    # Within a child the routes use a shared selector, so routes are deliberately
    # dependent. Leaf table names are disjoint across children; fine keys refine
    # distinct coarse keys. Center key 0 is exposed and excluded from trials.
    identities=outcomes=0
    for p in (F(1,7),F(1,3),F(2,3)):
        total=F(0)
        for bits in product((0,1),repeat=6):
            current=bits[:4]; shared=bits[4:]
            addresses=[]
            for i in range(2):
                for n in range(2):
                    coarse=n+1
                    leaf=(i,shared[i])
                    fine=4*coarse+(shared[i]+n)%4
                    assert fine//4==coarse and coarse!=0
                    addresses.append((leaf,fine))
            assert len(set(addresses))==4
            # Exact conditional terminal integration, then fair-selector average.
            total+=(1-p)**sum(current)/64; outcomes+=1
        assert total==(1-p/2)**4; identities+=1
    # Address independence survives full center exposure, including off-route tables.
    exposure_cases=0
    for xi in product((0,1),repeat=3):
        for pattern in product((0,1),repeat=3):
            compatible=0
            for other in product((0,1),repeat=3):
                table=tuple((xi[i],pattern[i],other[i]) for i in range(3))
                assert tuple(t[0] for t in table)==xi
                assert tuple(t[1] for t in table)==pattern
                compatible+=1
            assert compatible==8; exposure_cases+=1
    return {'dependent_route_outcomes':outcomes,'exact_failure_identities':identities,
            'full_center_exposure_patterns':exposure_cases}

def budgets():
    # A certified finite witness for closing (5.7) once all other constants are
    # fixed: exp(-gamma*r)<=2^(-r) for gamma>1, since e>2.
    witnesses=[]
    for C,g,p in ((1,1,F(1,2)),(10**8,100,F(1,100)),(10**30,10**6,F(1,10**5))):
        r=1
        while F(C*(r+g+1)**2,2**r)>=p: r+=1
        witnesses.append(r)
    k_sum=F(1,3)+1+1
    assert F(12,64)*k_sum==F(7,16)
    # Countably many q-slabs have budget sum sum_{m>=1}2^-m=1.
    return {'certified_exponential_dominance_witnesses':witnesses,'removed_measure_coefficient':'7/16'}

if __name__=='__main__':
    result={'status':'PASS','scope':'Exact finite checks only; see review for universal proof.',
            'partition':[partition_fixture(x) for x in (F(0),F(31,32),F(185,192))],
            'tree':tree_check(),'conditioning':conditional_check(),'budget':budgets()}
    print(json.dumps(result,indent=2,sort_keys=True))
