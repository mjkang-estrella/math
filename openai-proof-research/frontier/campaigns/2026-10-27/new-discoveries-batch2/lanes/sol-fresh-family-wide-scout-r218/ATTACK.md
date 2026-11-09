# Sustained attack: Sharma's primitive linearized-polynomial family

Target: Avnish K. Sharma, arXiv:2608.07262v3, Conjecture 4.1, printed p15. For every odd prime p and every positive even n, there is a primitive λ in K=F_(p^n) with δ=Σ_(i=0)^(n−1)(−1)^i λ^(p^i) nonzero such that X^p+X+λ is primitive over K. The introduction additionally asks the stronger n=2 assertion for EVERY primitive λ. These are one family, not two discoveries. The source's actual Proposition 4.1 proof, pp14–15, is the closest read theorem: it establishes irreducibility, not multiplicative primitivity.

## Route 1: conjugate orbit and exact reduction

Set L=F_(p^(np)), Q=p^n, and V={a in L : a^p+a belongs to K}. This is an F_p-linear space. Choose η in F_(p^2) with η^p=−η, η≠0; this exists since n is even. Writing a=ηb transforms a^p+a=λ into b^p−b=−λ/η. The Artin–Schreier image criterion on L is absolute trace zero. For any λ in K, the absolute trace of −λ/η from L is p times its trace from K and is zero. Thus every λ has p preimages in L and |V|=p^(n+1).

The target is EXACTLY that V contains a primitive element of L. In one direction a primitive root of the requested polynomial lies in V. Conversely take primitive a in V and put λ=−a^p−a. Its minimal polynomial over K has degree p, so it is the displayed polynomial. Its norm is −λ and is primitive in K, since the norm sends a generator of L* to a generator of K*. Also −λ primitive implies λ primitive: M=Q−1 is divisible by 4 and gcd(M/2+1,M)=1, so negation preserves generators. Finally δ≠0: iterating a^p=−a−λ n times gives a^Q=a+δ (n even); δ=0 would put a in K, contradicting its order Q^p−1. This proves the reduction, not existence of a primitive point in V.

The orbit computation also shows that for any δ≠0 all p roots are a+jδ, j in F_p, and are Frobenius conjugate over K. Therefore they all have the SAME multiplicative order. Testing one root per λ is sufficient; a search over p conjugates supplies no extra evidence. For n=2, δ=λ−λ^p. Primitive λ cannot lie in F_p, so δ≠0 automatically. This closes irreducibility for that stronger source question but does not close primitivity.

## Route 2: norm constraints, and why prescribed trace does not finish

The norm condition is necessary but is already automatic for primitive roots; it does not reverse. A primitive norm only forces the order of a to contain the appropriate factors from Q−1, not all prime factors of (Q^p−1)/(Q−1). The latter factors are the missing requirement. For n=2, direct iteration p times gives

    a^(p^p) = −a − (λ+λ^p)/2.

Indeed in the alternating sum of p conjugates of λ, the counts of λ and λ^p reduce modulo p to 1/2 and −1/2 respectively. Thus the relative trace to F_(p^p) equals −Tr_(K/F_p)(λ)/2. Prescribed-trace primitive-element theorems alone do not enforce a^p+a in K, let alone a specified λ. Sharma's actual p=2 argument uses Cohen's theorem because degree two has only trace and norm as free coefficients; at odd degree p there are p−2 additional vanishing coefficients. No full applicable bridge from Cohen's theorem has been established here. Cohen's original body was not retrieved; this is a limitation, not a claim that it cannot subsume the target.

## Route 3: elementary character sieve on V

Let M=|L*|, θ(M)=φ(M)/M and W(M)=2^ω(M). The ordinary primitive-element indicator, summed over V\{0}, has main term θ(M)(|V|−1). For a nontrivial multiplicative character χ of L, additive orthogonality and the Gauss-sum bound give |Σ_(a in V)χ(a)|≤sqrt(|L|): write the indicator of V using its annihilator and bound each nontrivial additive Gauss sum. The resulting sufficient inequality is

    p^(n+1)−1 > (W(M)−1) p^(np/2).

For n=2 this already fails at p=3: M=728 has three prime factors, so the right side is 7·27, versus 26 on the left. It fails still more strongly for p≥5 by exponents alone. This is a full comparison with a particular classical bridge, not an exclusion based on shortness. One needs cancellation exploiting V's special linearized structure, beyond the generic Gauss bound. The same analysis does not refute the conjecture.

## Route 4: exact finite attempts to refute the stronger n=2 statement

checks/finite_fields.py uses K=F_p[u]/(u²−d), where d is a least positive nonsquare. It tests ALL primitive λ for p=3,5,7,11. It computes in K[X]/(X^p+X+λ), verifies X^M=1, factors M exactly, and checks X^(M/r)≠1 for every prime r dividing M. Source irreducibility is guaranteed by δ≠0 as above. Results: respectively 4,8,16,32 primitive λ; no counterexample among these 60 λ. These exact computations support only these instances. They do not prove any universal conjecture or an absence of counterexamples elsewhere. No larger sweep was started.

## Decision

Strongest NEW-to-screen survivor, provisionally. No complete ordinary resolution, no PROOF.md, no nomination and no count. Decisive next step: locate/read the closest primitive-in-linear-subspace theorem with hypotheses retaining this very sparse V, or derive a non-generic character-sum estimate exploiting a^p+a∈K. A generic “large subspace” theorem is inadequate because dim(V)=n+1 while dim(L)=np. Current primary metadata search found the October18 version but is not a complete citing-body/registry clearance.
