# Counterexample to Yuster's polynomial-root conjecture (MathDB357503)

Working date: 2026-10-26. One proposed discovery; no claim of a smallest counterexample.

## Exact source statement

Raphael Yuster, *Almost k-union closed set systems*, arXiv:2302.12276v1 (23 February 2023), Corollary3.7 and Conjecture3.9. The conjecture asserts that for every integer k≥2 the real polynomial p_k has at most two roots in (0,1), counted with multiplicity. The source defines ψ_k as the unique solution of (1−ψ)^k=ψ on [0,1], φ_k=1−ψ_k, and α_k=φ_k^(k−1). Thus φ_k+φ_k^k=1 and α_k(1+α_k)^(k−1)=1.

The exact coefficient recurrence (Lemma3.5) is C(k,0,0)=1/(k−1)!, C(k,t,j)=0 when exactly one of t,j is zero, and

C(k,t,j)=(kj−t+1)C(k,t−1,j)+kC(k,t−1,j−1) (t,j>0).

Corollary3.7 gives p_k=α_k ρ_k−σ_k, where

ρ_k(x)=Σ_{j=0}^{k−1}(−1)^j j! C(k,k+1,j+2) [(x^k−1)^(k−j−1)x^(kj+k)−(x^k−1)^k],

σ_k(x)=Σ_{j=0}^{k−1}(−1)^j binom(k+1,j+2) [x^(j+1)(x−1)^(k−j−1)(Σ_{i=0}^{k−1}x^i)^k−(x^k−1)^k].

Our formal source polynomial is literally this expression; no unproved simplification or proxy polynomial is used.

## Exact certificate

Set k=48, a=61/1000, b=613/10000. Exact rational arithmetic proves

a(1+a)^47<1<b(1+b)^47.

The map u↦u(1+u)^47 is strictly increasing for u≥0; hence a<α_48<b.

At each of the five rational points x=1/100,1/10,1/2,3/5,4/5, the exact rational number ρ_48(x) is negative. The exact endpoint signs are

- aρ_48(1/100)−σ_48(1/100)<0;
- bρ_48(1/10)−σ_48(1/10)>0;
- aρ_48(1/2)−σ_48(1/2)<0;
- bρ_48(3/5)−σ_48(3/5)>0;
- aρ_48(4/5)−σ_48(4/5)<0.

Since ρ is negative, increasing α decreases p. These five signs therefore hold at α=α_48. The intermediate value theorem gives one root in each of

(1/100,1/10), (1/10,1/2), (1/2,3/5), (3/5,4/5).

These are pairwise disjoint open subintervals of (0,1); the four roots are distinct. Consequently the number of roots counted with multiplicity is at least four, disproving Conjecture3.9.

The certificate file `rootcount-exact-certificate.json` records the full rational endpoint values. `rootcount_exact_certificate.py` independently compares direct rational evaluation of the literal source formula with expanded integer-polynomial evaluation using FLINT. The three current Lean modules independently check the same exact rational signs in Lean's kernel (`decide +kernel`, not native_decide). Canonical α and the real sign transfer are being completed; parent supplies the final generic IVT/counting wrapper.

## Prior art and scope

This does not refute the underlying entropy inequality or a union-closed-set result. Boon Suan Ho, arXiv:2601.19327v1 (2026), proves the full generalized entropy inequality by a different route. That result does not imply this stronger proposed polynomial root count. Tanay Wakhare, arXiv:2312.14743v2 (2025), published J. Approx. Theory307(2025)106143, proposes a closely related root-count conjecture (Conjecture2); any claimed equivalence must be proved before separately identifying its scope. There is no separate discovery credit for equivalent formulations.

Targeted primary-source and current literature searches have not located a published root-count counterexample. This is a bounded prior-art check, not a certificate of worldwide priority. Independent source, mathematics, arithmetic, and novelty review is pending. No minimality of k=48, exact total root count, or effect on the already proved entropy inequality is claimed.
