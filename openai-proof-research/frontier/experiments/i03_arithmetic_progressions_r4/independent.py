"""Exact finite algebra only; no test of asymptotic analytic inputs."""
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import json
out=Path(__file__).resolve().parent
stats={}
# Independently count solutions by the forced t=d^{-1}; all composite/prime-power moduli.
cases=nonunits=0
for M in range(2,97):
    units=[t for t in range(M) if gcd(t,M)==1]
    for d in units:
        inv=pow(d,-1,M)
        for r in range(M):
            valid=[w for w in range(M) if inv*w%M==r and inv*(w+d)%M==(r+1)%M]
            assert valid==[r*d%M]
            cases+=M;nonunits+=M*(gcd(r,M)>1)
stats['orbit_extended']={'cases':cases,'nonunit_source_cases':nonunits,'failures':0,'max_modulus':96}
# Physical shared counting weights need not be residue independent before 1/n.
# Two possible label magnitudes for each unit residue, with residue-dependent probabilities.
weighted_cases=0; biased_dyads=0
for M in range(2,14):
    units=[t for t in range(M) if gcd(t,M)==1];phi=len(units)
    law=[]
    for t in units:
        a=F(t,M)
        law += [(M+t,a/phi),(2*M+t,(1-a)/phi)]
    assert sum(p for _,p in law)==1
    for c in units[:3]:
        for d0 in units:
            d=d0+M; x=3
            for r in range(M):
                physical=F(0); stripped=F(0); bins={}; comparison_bins={}
                for w in range(1,2*x*d+1):
                    z=F(w,x*d)
                    psi=(z-1)*(2-z) if 1<z<2 else F(0)
                    # Arbitrary signed remaining coefficient depending on w and free d.
                    coeff=F((w*w+3*d*w)%17-8,9)
                    bare=psi*coeff/w
                    stripped += bare/phi*((w-r*d)%M==0)
                    for label,mu in law:
                        R=c*label;n=R*w;target=R*(w+d)
                        cutoff=F(n,x*R*d)
                        assert cutoff==z
                        term=mu*R*psi*coeff/n
                        assert term==mu*bare
                        indicator=(n%M==r and target%M==(r+1)%M)
                        physical+=term*indicator
                        j=n.bit_length()-1
                        bins[j]=bins.get(j,F(0))+term*indicator
                        comparison_bins[j]=comparison_bins.get(j,F(0))+term/phi*((w-r*d)%M==0)
                assert physical==stripped==sum(bins.values())
                biased_dyads+=any(bins[j]!=comparison_bins[j] for j in bins)
                weighted_cases+=1
stats['weighted_stripping_reassembled']={'cases':weighted_cases,'failures':0,'cases_with_individually_biased_dyads':biased_dyads}
# CRT main term: enumerate one full modulus, including sieve moduli sharing M.
ct=0;shared=0
for M in range(2,19):
    for b in range(M):
        if gcd(b,M)>1:continue
        for r in range(1,22):
            for ld in range(1,13):
                if gcd(ld,M)>1:continue
                count=sum((ld*v+1)%r==0 and (ld*v+1-b)%M==0 for v in range(M*r))
                expected=int(gcd(r,M)==1 and gcd(ld,r)==1)
                assert count==expected,(M,b,r,ld,count)
                ct+=1;shared+=gcd(r,M)>1
stats['CRT_main']={'cases':ct,'noncoprime_sieve_modulus_cases':shared,'failures':0}
# A perturbed residue distribution yields uniform O(delta) orbit error, even with
# arbitrary independent other shared residue. Conditioning on arithmetic acceptance
# itself would instead bias the shared residue, and is deliberately NOT done.
ct=0
for M in range(2,25):
    units=[t for t in range(M) if gcd(t,M)==1];phi=len(units)
    if phi<2:continue
    delta=F(1,5*phi)
    probs={t:F(1,phi) for t in units}
    probs[units[0]]+=delta;probs[units[-1]]-=delta
    for c in units:
        for d in units:
            for w in range(M):
                for r in range(M):
                    t=(pow(d,-1,M)*pow(c,-1,M))%M
                    val=probs[t] if w%M==r*d%M else 0
                    expected=F(int(w%M==r*d%M),phi)
                    assert abs(val-expected)<=delta
                    ct+=1
stats['uniform_conditioned_orbit_error']={'cases':ct,'failures':0}
(out/'independent-results.json').write_text(json.dumps(stats,indent=2)+'\n')
print(json.dumps(stats,indent=2))
