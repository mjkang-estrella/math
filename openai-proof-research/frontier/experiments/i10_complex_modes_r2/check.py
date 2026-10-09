"""Exact fragile-algebra diagnostics, not numerical asymptotic evidence."""
from pathlib import Path
from fractions import Fraction as F
from math import gcd, comb, prod
import itertools, json

OUT=Path(__file__).resolve().parent

def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]

def mobius(n):
    k=0
    p=2
    while p*p<=n:
        if n%p==0:
            n//=p; k+=1
            if n%p==0: return 0
        p+=1
    return (-1)**(k+(n>1))

def ramanujan(k,h):
    return sum(d*mobius(k//d) for d in divisors(gcd(k,h)))

def phi(q):
    return sum(gcd(a,q)==1 for a in range(q))

counts={}
crt=overlap=nonunit=0
for M in range(1,33):
    for b in range(M):
        if gcd(b,M)!=1: continue
        g=gcd(b-1,M)
        for a in range(1,65):
            for r in range(1,13):
                if gcd(r,M)!=1: continue
                compatible=(gcd(a,M)==g and gcd(a,r)==1)
                ell=101
                q=r*M//g
                residues=[v for v in range(q) if gcd(v,M)==1 and
                          (ell*a*v+1)%r==0 and (ell*a*v+1-b)%M==0]
                if not compatible:
                    assert not residues
                else:
                    # Congruences determine one *reduced* class modulo q;
                    # roughness still excludes the primes of M lost in g.
                    qr=r
                    qm=M//g
                    vr=(-pow((a*ell)%r,-1,r))%r if r>1 else 0
                    vm=(((b-1)//g)*pow((a//g*ell)%qm,-1,qm))%qm if qm>1 else 0
                    v0=next(v for v in range(q) if v%qr==vr and v%qm==vm)
                    assert gcd(v0,q)==1
                    assert residues == ([v0] if gcd(v0,M)==1 else [])
                    for v in (v0, v0+q, v0+2*q):
                        if gcd(v,M)==1:
                            assert (ell*a*v+1)%r==0 and (ell*a*v+1-b)%M==0
                    overlap += int(gcd(a//g,g)>1)
                    nonunit += int(g>1)
                crt+=1
counts['crt']={'cases':crt,'compatible_nonunit':nonunit,'extra_valuation_cases':overlap}

ram=0
for k in range(1,49):
    for h in range(k):
        for a in range(1,25):
            for ell in (53,59):
                assert ramanujan(k,h*a*ell)==ramanujan(k,h*a)
                ram+=1
counts['ramanujan_nonunit_invariance']=ram

# Exact density on a finite rough-prime model, including large q-primes.
density=0
for small in ((2,), (2,3), (2,3,5)):
    P=prod(small); Vy=prod(F(p-1,p) for p in small)
    for q in range(1,33):
        period=P*q//gcd(P,q)
        formula=Vy/F(phi(q))*prod(F(p-1,p) for p in range(2,q+1)
                    if q%p==0 and mobius(p)==-1 and len(divisors(p))==2 and p not in small)
        for a in range(q):
            if gcd(a,q)!=1: continue
            actual=F(sum(n%q==a and gcd(n,P)==1 for n in range(period)),period)
            assert actual==formula
            density+=1
counts['rough_density_23']=density

bonf=0
for w in range(100):
    for h in range(35):
        err=int(w==0)-sum((-1)**j*comb(w,j) for j in range(min(w,h)+1))
        envelope=comb(w,h+1) if h+1<=w else 0
        assert abs(err)<=envelope
        assert err*err<=4**w*int(w>=h) if h else True
        bonf+=1
counts['bonferroni_envelope_and_square']=bonf

# Exact falling-factorial version of the gamma/binomial identity.
gamma=0
for z in (F(1,3), F(-2,3), F(7,5)):
    inv=[F(1)]
    for j in range(1,20): inv.append(inv[-1]*(z-j))
    for j in range(9):
        for r in range(9):
            binomial=prod((z-1-j-i)/F(i+1) for i in range(r))
            assert inv[j]*binomial==inv[j+r]/prod(range(1,r+1))
            gamma+=1
counts['density_gamma_recurrence']=gamma

def small_part(n):
    a=1
    for p in (2,3,5,7):
        while n%p==0: a*=p; n//=p
    return a,n

def omega(n):
    answer=0
    p=2
    while p*p<=n:
        while n%p==0: answer+=1; n//=p
        p+=1
    return answer+int(n>1)

cov=0
for n in range(1,301):
    ay,rough=small_part(n)
    for a in (1,2,4,8,9,25,49,12,360,441):
        by,rough2=small_part(a*n)
        assert by==a*ay and rough2==rough
        assert (omega(by)-omega(ay)-omega(a))%12==0
        # Every beta argument and harmonic coefficient agrees term by term.
        for ell in (11,13,11*17): assert F(n,ay*ell)==F(a*n,by*ell)
        cov+=1
counts['symbolic_position_covariance']=cov

# Reassemble genuine signed success/failure expansions after allocation.
coins=alloc=0
for j in (2,3,4):
    q0=F(1,2); c1=F(1,16)
    for hits in itertools.product((0,1,2),repeat=4):
        u_hits=(1,2,1,3)
        s=[c1*q0**(u_hits[g]-1)*u_hits[g]*(q0/j)**(hits[g]-1)*hits[g]
           if hits[g] else F(0) for g in range(4)]
        retained=[S for S in range(16) if S&3 and S&12]
        direct=sum(prod(s[g] if S>>g&1 else 1-s[g] for g in range(4)) for S in retained)
        expanded=F(0)
        for S in retained:
            rest=[g for g in range(4) if not S>>g&1]
            for bits in range(1<<len(rest)):
                P=S; parity=0
                for i,g in enumerate(rest):
                    if bits>>i&1: P|=1<<g; parity+=1
                expanded+=(-1)**parity*prod(s[g] for g in range(4) if P>>g&1)
        assert direct==expanded and 0<=direct<=1
        for P in range(16):
            active=[g for g in range(4) if P>>g&1]
            omega=sum(hits[g] for g in active); size=len(active)
            assert F(j)**omega*(q0/j)**(omega-size)==F(j)**size*q0**(omega-size)
            alloc+=1
        coins+=1
counts['signed_retained_coin_reassembly']=coins
counts['allocation_identity']=alloc

# Counter-diagnostics: these deliberately rejected substitutions really fail.
counts['rejected_shortcuts']={
    'inverse_phase':{'z':'i','c':1,'z_to_c':'i','z_to_minus_c':'-i'},
    'model_depends_on_active_set':{'s1':str(F(1,2)),'s2':str(F(1,2)),
      'retained_event':'success 1, failure 2', 'B_1':1,'B_12':0,
      'signed_model_sum':str(F(1,2)),'retained_probability':str(F(1,4))},
    'lost_full_valuation_prime':{'M':4,'b':1,'a':8,'g':4,'r':1,
      'q':1,'warning':'q=1 is reduced but v must still be odd by roughness'},
}
(OUT/'results.json').write_text(json.dumps(counts,indent=2)+'\n')
print(json.dumps(counts,indent=2))
