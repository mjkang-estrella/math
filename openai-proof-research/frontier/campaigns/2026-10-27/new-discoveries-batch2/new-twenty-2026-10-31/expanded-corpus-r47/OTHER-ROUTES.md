# Sustained secondary routes

## 354171 — positive weighted hypercube extremal designs

Read primary definitions and Section 5.3–5.4, Lemma 5.9, Theorem 5.13, Corollary 5.14, Bonisoli Theorem 5.15 as stated, Lemma 5.16 and its proof, Theorem 5.17 and its proof, Conjecture 5.19 and Example 5.20. Bonisoli's original paper is NOT body-read. The source itself carefully distinguishes optimality among linear constant-weight constructions from the asserted global positive-weight optimum.

A probability weight f on {0,1}^d averages all Walsh characters except level m iff its Fourier support is contained in {0} union level m. Here m=d/2 (d=0 mod4), (d-1)/2 (d=1 mod4), or (d+1)/2 (d=3 mod4), with frequency tie chosen as in source. The proposed code support has size 2^(d-t), t=ν2(2m). Exact Walsh sums for d=7,8,9,11 reproduced the existing constructions in diagnostics.py; these are diagnostic confirmations of known constructions, not new results.

Attempt 1: classify linear codes via Bonisoli. This proves only optimal linear-code support, already in the paper. It cannot establish Conjecture 5.19.

Attempt 2: write f=2^-d(1+h), with adjacency eigenfunction A h=(d-2m)h and h≥-1. When d=3 mod4, m=(d+1)/2, A f+f=(d+1)2^-d. Every vertex is in the closed neighborhood of the positive support, whence |supp f|≥ceil(2^d/(d+1)). At d=7 this is 16, attained by the known code. At d=11 it is only 171 versus the proposed 512. This is a real full-positive-weight lower bound, but is much too weak; do not turn a solved small dimension into credit.

Attempt 3: tensor or sum small cube eigenfunctions. Products of the nonnegative densities have mixed Fourier levels, violating the exact endpoint. Products of centered single-level h keep a single level but can have negative minima too large: for a density with h∈{-1,3}, the product can attain -3, so 1+h1*h2 is not nonnegative. Rescaling by 1/3 restores positivity but worsens support. Sums need the same Fourier level and likewise fail to attain the proposed support density. These mechanisms do not produce a counterexample.

Precise remaining lemma: prove |supp(1+h)|≥2^(d-ν2(2m)) for every real level-m Walsh polynomial h with h≥-1 and uniform mean zero, in the indicated middle levels; OR construct a single violating h with rational nonnegative weights and certify every outside-level Walsh coefficient is zero. No universal bound of that strength has been proved here. No LP output or finite scalar bound is a literal Lean endpoint. Park.

## 354003 — Eisenstein polynomial contents

Read equation (3), normalization Gk=2ζ(k)Ek, Popa recurrence Proposition 2, digit-sum Lemmas 5–6 and proof, Theorem 7 and complete induction proof, Conjecture 8, Lemma 10 and its proof using (12). Source s(k) is written without subscript in Conjecture 8; earlier notation s2 denotes binary digit sum. This interpretation must be independently checked for final fidelity. Rational valuation includes ν2(0)=infinity. Primary conjecture was already verified through weight 3500; repeating a small numerical sweep would not advance it.

Attempt 1: use Rademacher's recurrence (12) in Q[G4,G6]. For k divisible by 4, all factors in (k/2-3)(k-1)(k+1) are odd. Pair p and k/2-p; modulo 2 all paired terms vanish, leaving an odd multiple of G_(k/2)^2 (for k≥8). Combined with source Theorem 7, this proves the polynomial is congruent modulo 2 to its half-weight square. Thus zero content propagates along powers-of-two doubling of weights 4 and 6. This only recovers the power-of-two and two-bit special patterns, overlapping source Lemma 10; no new count.

Attempt 2: normalize the full recurrence by 2^(s2(k)-2) and try to induct on binary digits. The paired terms and central square can have the same valuation, so a lower bound on separate summands cannot prove a coefficient survives modulo 2. When k=2 mod4 the denominator k/2-3 is even, adding a further divisibility obligation; Theorem 7 uses a different differential recurrence precisely to handle integrality. There is no proved no-cancellation statement for the normalized polynomial.

Precise remaining lemmas: all rational coefficients are divisible in Z_(2) by 2^(s2(k)-2), and the normalized polynomial has a nonzero coefficient modulo 2 for every non-power-of-two k. The second statement is not implied by Theorem 7. No modular-form-to-polynomial Lean bridge or universal noncancellation proof was found. Park; no diagnostic sweep or formal surrogate.

## Exclusions with new body review

353711: primary Conjecture 1.1 and actual Theorem 3.3/proof were read. The stress-space rank argument proves the edge bound exactly. Minimum-degree ≤2d+1 follows by the counting observation stated there (average degree <2d+2). This is already solved in the cited source, not a discovery.

354369: source Definition 1.1, Theorem 1.3, Conjecture 1.4 were read, then Iskander arXiv:2310.18798v2 Theorems 1.5–1.7 statements, Counterexample 1.8 and displayed degree-11 polynomial, and code availability discussion. The counterexample k=14, λ=(2,1) has nine real roots and two nonreal roots; it addresses exactly the real-rootedness conjunct, so this conjunctive MathDB assertion is already refuted. Full Iskander derivation and accompanying exact computation code were NOT audited. No new priority or positivity resolution claimed.

354173: Fox–Himwich–Mani Section 5 Conjecture 5.6 and adjacent blowup construction were read. Kai Lum's MIT-hosted paper, actual Theorem 1.5 and proof Section 2.1 were read. The abstract's ceiling wording differs from the theorem's floor wording: the BODY states r>floor(2n/3), equivalent to r>2n/3 for integer r, and claims the exact endpoint. The proof has rounding inconsistencies in its prose, and its deviate-path simplification deserves review; do not represent it as an independently validated theorem. It is nevertheless a prior public claimed full-scope proof, sufficient to withhold a NEW-solution claim pending comparison. No technical acceptance of Lum's proof here.
