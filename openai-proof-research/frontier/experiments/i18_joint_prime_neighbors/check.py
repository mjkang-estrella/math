"""Exact finite I18 diagnostics. No numerical evidence for asymptotics."""
from pathlib import Path
from fractions import Fraction as F
from math import gcd, lcm
import json

OUT = Path(__file__).resolve().parent

def phi(n):
    return sum(gcd(a, n) == 1 for a in range(n))

def valuation(n, q):
    e = 0
    while n and n % q == 0:
        e += 1
        n //= q
    return e

def run():
    counts = dict(crt=0, compatible=0, nonunit_neighbor=0,
                  prime_residue_crt=0, local_valuation=0,
                  prime_factor_tuple_identities=0, failures=0)
    for a in range(1, 9):
        for b in range(1, 9):
            for m in range(1, 7):
                for c in range(m):
                    if gcd(c, m) != 1:
                        continue
                    for r in range(1, 7):
                        period = lcm(a, b, m, r)
                        hits = [n for n in range(period) if
                                (n-1) % a == 0 and (n+1) % b == 0
                                and (n-c) % m == 0 and n % r == 0]
                        compatible = (2 % gcd(a, b) == 0
                                      and (c-1) % gcd(a, m) == 0
                                      and (c+1) % gcd(b, m) == 0
                                      and gcd(r, a*b*m) == 1)
                        assert len(hits) == int(compatible), (a,b,m,c,r)
                        counts['crt'] += 1
                        counts['compatible'] += compatible
                        counts['nonunit_neighbor'] += bool(compatible and
                            (gcd(c-1,m)>1 or gcd(c+1,m)>1))
                    period = lcm(a,b,m)
                    hits = [n for n in range(period) if
                            (n-1)%a == 0 and (n+1)%b == 0 and (n-c)%m == 0]
                    assert all(gcd(n,period)==1 for n in hits)
                    counts['prime_residue_crt'] += 1
    for q in [3,5,7,11]:
        kmax = 3
        mod = q**(kmax+1)
        units = [a for a in range(mod) if gcd(a,mod)==1]
        for k in range(1,kmax+1):
            for sign in [-1,1]:
                mass = F(sum(valuation(a+sign,q)==k for a in units),len(units))
                assert mass == F(1,q**k), (q,k,sign,mass)
                counts['local_valuation'] += 1
        neither=F(sum((a-1)%q != 0 and (a+1)%q != 0 for a in units),len(units))
        assert neither==F(q-3,q-1)
        counts['local_valuation'] += 1
    mod=2**8
    units=list(range(1,mod,2))
    for k in range(2,7):
        for left,right in [(1,k),(k,1)]:
            mass=F(sum(valuation(a-1,2)==left and valuation(a+1,2)==right for a in units),len(units))
            assert mass==F(1,2**k)
            counts['local_valuation'] += 1
    # Raw target symmetrization: physical source (462;3,7), target (465;3,5).
    target=465
    correct=int((target//3+1)%13==0)
    sym=F(sum((target//d+1)%13==0 for d in [3,5]),2)
    assert correct==1 and sym==F(1,2)
    covariance={'h':33,'labels':[3,5],'long_prime':101,
                'shifted_values':[(a*33+2)%101==0 for a in [3,5]],
                'undilated_value':(33+2)%101==0}
    assert covariance['shifted_values']==[True,False]
    # A rare label can carry a different joint law with exact fair marginals.
    mixture=[]
    for k in [2,4,8,16,32,64]:
        delta=F(1,k)
        weights={(i,j):(1-delta)*F(1,4)+(delta*F(1,2) if i==j else 0)
                 for i in [0,1] for j in [0,1]}
        assert all(sum(v for (i,j),v in weights.items() if i==a)==F(1,2) for a in [0,1])
        assert all(sum(v for (i,j),v in weights.items() if j==a)==F(1,2) for a in [0,1])
        tv=sum(abs(v-F(1,4)) for v in weights.values())/2
        assert tv==delta/2
        mixture.append({'rare_mass':str(delta),'unconditional_tv':str(tv),
                        'conditional_tv':'1/2'})
    # Two-colored divisor counting identity, tested as an identity only.
    primes=[n for n in range(2,501) if all(n%d for d in range(2,int(n**.5)+1))]
    for lo,hi in [(20,70),(70,140),(140,300)]:
        for left in [[3,5],[5,7,11],[11,13,17]]:
            for right in [[3,7],[5,11,13],[17,19,23]]:
                direct=sum(sum((p-1)%a==0 for a in left)*sum((p+1)%b==0 for b in right)
                           for p in primes if lo<p<=hi)
                swapped=sum(sum(lo<p<=hi and (p-1)%a==0 and (p+1)%b==0
                                for p in primes) for a in left for b in right if gcd(a,b)==1)
                assert direct==swapped
                counts['prime_factor_tuple_identities'] += 1
    return {'scope':'finite identities only; no asymptotic test', 'counts':counts,
            'covariance_counterexample':covariance,
            'target_symmetrization':{'source':462,'target':465,'source_marks':[3,7],
                'target_marks':[3,5],'long_prime':13,'desired':correct,'symmetric_value':str(sym)},
            'rare_conditioning_countermodels':mixture}

if __name__=='__main__':
    result=run()
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
