# MathDB 342364: complete resolution of Ulas–Żmija Conjecture 6.1

Status: round 3 partial formalization. The faithful functional equation, full-series even-section operator, general-j readout, parity, and universal n=1 polynomial are now proved. All six Remaining Props are still open. Round 3 proves the explicit reduced operator weight estimates and constant coefficient formula, separately from the missing series bridge. The complete ordinary argument below is not a complete Lean proof. Not accepted.

## 0. The statement and its source

Source: M. Ulas and B. Żmija, "On p-adic valuations of certain m colored p-ary partition functions", arXiv:1904.03398 (only v1 exists, checked 2026-11-03), published in Ramanujan J. 55 (2021) 623–660. Section 6 of both versions states Conjecture 6.1 in the same words.

Definitions (source, Introduction and Section 2):

    G_2(x) = 1/(1-x) * prod_{i>=0} 1/(1-x^{2^i}),   C(x) := G_2(x),   C(x)^m = sum_n c_m(n) x^n.

So c_m(n) counts binary partitions of n in which the part 1 takes one of 2m colours and every larger part takes one of m colours; c_1(n) = b(2n).

**Conjecture 6.1 (literal text).** For k ∈ N_+ and each n ∈ N_+,

    nu2(c_{2k}(4n) - c_{2k}(n)) = nu2(n) + 2 nu2(k) + 3.

Moreover, for k ∈ N and n ∈ N_+,

    nu2(c_{4k+1}(4n) - c_{4k+1}(n)) >= nu2(n) + 3,
    nu2(c_{4k+3}(4n) - c_{4k+3}(n)) >= nu2(n) + 6.

In each case the equality holds for infinitely many n ∈ N.

The source reports numerical evidence only for m ∈ {2,…,10} and n <= 10^5. The MathDB statement (raw line in raw/342364.jsonl) reproduces this text.

## 1. Result

**Theorem.** Let n >= 1.

1. (Even m.) For every k >= 1, nu2(c_{2k}(4n) - c_{2k}(n)) = nu2(n) + 2 nu2(k) + 3.
2. (m ≡ 1 mod 4.) For every k >= 0, nu2(c_{4k+1}(4n) - c_{4k+1}(n)) >= nu2(n) + 3, with equality for every odd n.
3. (m ≡ 3 mod 4.) For every k >= 0, nu2(c_{4k+3}(4n) - c_{4k+3}(n)) >= nu2(n) + 6. Moreover:
   * if m ≡ 3 or 7 (mod 16), equality holds for every odd n;
   * if m ≡ 11 (mod 16), equality holds for every n ≡ 2 (mod 4);
   * if m ≡ 15 (mod 16), that is k ≡ 3 (mod 4), then nu2(c_m(4n) - c_m(n)) >= nu2(n) + 7 for **every** n, so equality **never** holds.

Consequently every inequality and the even-case equality of Conjecture 6.1 are true. The final clause ("in each case the equality holds for infinitely many n") is **false** for every k ≡ 3 (mod 4), the first case being m = 15 (k = 3), just beyond the authors' verified range m <= 10. For example, c_15(4) - c_15(1) = 48030 - 30 = 48000 = 2^7 · 375, so nu2 = 7 at n = 1. The bound nu2(n)+6 is never attained for m = 15, 47, 79, …. Numerically (outputs below), the sharp constant for m ≡ 3 mod 4 is max(6, nu2(m+1)+3); this refinement is recorded but not claimed.

## 2. Operator framework

Put y = x/(1-x) and w = (1+x)/(1-x) = 1 + 2y. Every polynomial F ∈ Z[y] is an integral power series in x, because y^E = x^E (1-x)^{-E} has coefficients binom(n-1,E-1). Write U_2 for the even section, U_2(sum a_n x^n) = sum a_{2n} x^n.

(F1) C(x) = w · C(x^2). Indeed C(x) = (1-x)^{-2} prod_{i>=1}(1-x^{2^i})^{-1} and C(x^2) = (1-x^2)^{-1} prod_{i>=1}(1-x^{2^i})^{-1}, whose ratio is (1+x)/(1-x).

(F2) Hence for a rational function F with poles only at x = 1: U_2(C^m F) = C^m · T(F), where T(F) := U_2(w^m F), because U_2(g(x) h(x^2)) = h(x) U_2(g(x)).

(F3) Chebyshev form of U_2. If P is a polynomial (or Laurent polynomial) in w, then U_2(P(w))(x^2) = (P(w) + P(1/w))/2, since x -> -x sends w to 1/w. The right-hand side is a polynomial in s = (w + 1/w)/2 = (1+x^2)/(1-x^2), which is the "w" of the variable x^2. Hence U_2(w^k) = T_k(w) (Chebyshev polynomial of the first kind), with the convention T_{-k} = T_k. For the new variable, s - 1 = (w-1)^2/(2w), so y_new := (s-1)/2 satisfies (w-1)^2 = 4 w y_new. With y = (w-1)/2 this gives

    y^{2e} = w^e y_new^e,    y^{2e+1} = w^e y_new^e (w-1)/2.

Let D_m(x) := sum_n (c_m(4n) - c_m(n)) x^n and A_j := T^j(1). By (F2), sum_n c_m(2^j n) x^n = C^m A_j, so

    U_2^j D_m = C^m d_j,   d_j := A_{j+2} - A_j = T^j(d_0),   and   c_m(4 · 2^j o) - c_m(2^j o) = [x^o] C^m d_j.   (1)

(F4) The parity of C. Since w = 1 + 2y ≡ 1 (mod 2), (F1) gives C(x) ≡ C(x^2) (mod 2) coefficientwise. So c_1(n) ≡ [n even] c_1(n/2) (mod 2), hence c_1(n) is even for n >= 1, and C^m ≡ 1 (mod 2) for every m >= 1. This is also a special case of the source's Theorem 2.4.

## 3. The reduced operators

The operator preserves ℤ[y]: the even rule is integral, and T_{N+1}(w)−T_N(w)=(w−1)W_N(w) makes the odd rule y^{e+1}W_{m+e}(1+2y) integral. Since T(F)(w=1) = F(1) and T(F)(w=-1) = (-1)^m F(-1), every d_j vanishes at w = ±1. So d_j is divisible in Z[y] by (w^2-1)/4 = y(1+y), which is monic.

**Lemma R (reduced operator).** For R ∈ Z[y], T(y(1+y) R) = y(1+y) · T~(R), where T~ is the Z-linear map

    T~(y^{2e})   = 2 y^e U_{m+e}(1+2y)            = 2 y^e sum_{i>=0} 4^i binom(m+e+i+1, 2i+1) y^i,
    T~(y^{2e+1}) =   y^e (U_{m+e+1}-U_{m+e})(1+2y) =   y^e sum_{i>=0} 4^i binom(m+e+i+1, 2i)   y^i.

*Proof.* y(1+y) = w(w - w^{-1})/4. Put G = w^{m+1}R. Then

    U_2(w^m y(1+y) R)(x^2) = (w-w^{-1})(G(w) - G(1/w))/8 = (w-w^{-1})^2 Ψ(G)/8 = (s^2-1)/2 · Ψ(G),

where Ψ(G) = (G(w)-G(1/w))/(w-w^{-1}) satisfies Ψ(w^k) = U_{k-1}(s). In the new variable, s^2 - 1 = 4 y_new(1+y_new). The displayed rules follow from y^{2e} = w^e y_new^e and y^{2e+1} = w^e y_new^e (w-1)/2, together with the expansions

    U_N(1+t) = sum_i binom(N+i+1, 2i+1) 2^i t^i,   U_{N+1}(1+t) - U_N(1+t) = sum_i binom(N+i+1, 2i) 2^i t^i,

taken at t = 2y. The first expansion is classical. The second follows from Pascal's rule. ∎

So d_j = y(1+y) r_j with r_{j+1} = T~(r_j).

**Weight.** For R = sum R_E y^E ∈ Z[y], put ω(R) := min_E (nu2(R_E) - bitlen(E)), where bitlen(0) = 0 and bitlen(E) = floor(log2 E) + 1 otherwise.

**Lemma W.** If ω(R) >= w, then

    T~(R) = sum_{e>=0} R_{2e+1} y^e + 2(m+1) R_0 + H,   with ω(H) >= w + 2.

In particular ω(T~(R)) >= ω(R) + 1 (the main terms have weight >= w+1).

*Proof.* Check each monomial contribution, using nu2(4^i · integer) >= 2i and bitlen(a+b) <= bitlen(a) + bitlen(b) for a, b >= 1.
* E = 2e with e >= 1, term i >= 0: weight >= 1 + 2i + w + bitlen(2e) - bitlen(e+i) >= w + 2 + 2i - bitlen(i) >= w + 2.
* E = 0, term i >= 1: weight >= 1 + 2i + w - bitlen(i) >= w + 2.
* E = 2e+1, term i >= 1: weight >= 2i + w + bitlen(2e+1) - bitlen(e+i) >= w + 1 + 2i - bitlen(i) >= w + 2.
* The remaining terms are E = 2e+1 with i = 0, giving R_{2e+1} y^e, of weight >= w + bitlen(2e+1) - bitlen(e) = w + 1; and E = 0 with i = 0, giving 2(m+1)R_0, of weight >= w + 1. ∎

Also, exactly: [y^0] T~(R) = 2(m+1) R_0 + R_1.

**Readout.** If r_j ∈ 2^a Z[y], then by (1) the difference at n = 2^j o is divisible by 2^a, for every o >= 1. If moreover nu2(r_{j,0}) = a and nu2(r_{j,E}) >= a+1 for all E >= 1, then by (F4), for odd o,

    [x^o] C^m y(1+y) r_j ≡ r_{j,0} [x^o] x/(1-x)^2 = r_{j,0} · o   (mod 2^{a+1}),

so the valuation at n = 2^j o equals a exactly.

## 4. Even m = 2k

Here T(1) - 1 = T_{2k}(w) - 1 = 2(T_k(w)^2 - 1) = 2(w^2-1) U_{k-1}(w)^2 = y(1+y) ρ with ρ := 8 U_{k-1}(1+2y)^2. Then d_0 = (T+1)(T(1)-1) gives r_0 = ρ + T~(ρ).

Put a := 3 + 2 nu2(k). Write U_{k-1}(1+2y) = sum_a' u_{a'} y^{a'} with u_{a'} = 4^{a'} binom(k+a', 2a'+1). The identity

    binom(k+a,2a+1) · (2a+1) · binom(2a,a) = k · binom(k+a,a) · binom(k-1,a)

and Kummer's nu2(binom(2a,a)) = s_2(a) (binary digit sum) give nu2(binom(k+a,2a+1)) >= nu2(k) - s_2(a). Hence

    nu2(ρ_E) >= a + 2E - max_{b+c=E}(s_2(b) + s_2(c)) >= a + E.

Invariant I(R, v): ω(R) >= v; nu2(R_0) = v; and nu2(R_{2^i - 1}) >= v + i + 1 for every i >= 1.

* I(ρ, a) holds. ρ_0 = 8k^2 has valuation exactly a. ω(ρ) >= a because a + E >= a + bitlen(E). For i = 1: ρ_1 = 64 k binom(k+1,3), of valuation >= 6 + nu2(k) + nu2(k) - 1 = a + 2. For i >= 2: the pair (b,c) with b+c = 2^i - 1 has no carries, so s_2(b)+s_2(c) = i and nu2(ρ_{2^i-1}) >= a + 2^{i+1} - 2 - i >= a + i + 1.
* Step: if I(R, v) holds and m is even, then I(T~(R), v+1) holds. By Lemma W, T~(R) = sum_e R_{2e+1}y^e + 2(m+1)R_0 + H with ω(H) >= v+2. The constant term is 2(m+1)R_0 + R_1 + H_0, whose three parts have valuations v+1 (m+1 is odd), >= v+2 and >= v+2, so it has valuation exactly v+1. The coefficient at 2^i - 1 is R_{2^{i+1}-1} + H_{2^i - 1}, of valuation >= min(v+i+2, v+2+i).
* So I(T~ρ, a+1) holds, and r_0 = ρ + T~ρ satisfies I(r_0, a): T~ρ changes no coefficient at the levels that matter. By induction, I(r_j, a+j) for all j.

By the readout, for n = 2^j o with o odd, nu2(c_{2k}(4n) - c_{2k}(n)) = a + j = nu2(n) + 2 nu2(k) + 3. ∎ (Part 1)

## 5. Odd m = 2h+1

Here T(1) + 1 = T_m(w) + 1 = (w+1) W_h(w)^2, where W_h = U_h - U_{h-1} is the fourth-kind Chebyshev polynomial, cos((2h+1)φ)/cos φ evaluated at cos 2φ. Hence d_0 = (T-1)(T_m(w)+1) = 2(1+y) · (T'-1)(G) with G := W_h(1+2y)^2. Here T' is defined by T(2(1+y)H) = 2(1+y) T'(H) (half-angle computation, z = w^{1/2}):

    T'(y^{2e}) = y^e W_{m+e}(1+2y) = y^e sum_i 4^i binom(m+e+i, 2i) y^i,
    T'(y^{2e+1}) = 2 y^{e+1} U_{m+e}(1+2y).

Since T'(H)(y=0) = H(y=0), (T'-1)G is divisible by y, and r_0 = 2 · ((T'-1)G)/y.

**Crude bound.** The coefficients γ_E of G satisfy nu2(γ_E) >= 2E. Tracking each term into [y^{F+1}](T'-1)G gives contributions of valuation >= 2F+2 (from even E), >= 2F+3 (from odd E), and >= 2F+2 (from the -G term). Hence

    nu2(r_{0,F}) >= 2F + 3   for all F >= 0.   (2)

**Low coefficients.** By direct expansion, r_{0,0} = [y]A_2 = 2m^2 + (2/3)m^2(m^2-1) + 2m^2(2m+1) = (2/3) m^2 (m+1)(m+5). From the expansion of A_2 in the τ-coefficients of T_m(1+2y), the coefficient r_{0,F} has degree at most 4F+4 in m. Indeed τ_{m,i} has degree 2i. For i=2e, the contribution to [y^E]A_2 has degree at most 4e+2(E−e)=2E+2e ≤ 4E. For i=2e+1, [y^{E−e}](T_{m+e+1}−T_{m+e}) has degree at most 2(E−e)−1, since it is a first difference in m. When e=E the constant coefficient difference is zero; otherwise e ≤ E−1, so the total degree is at most 4e+2+2(E−e)−1 ≤ 4E−1. Finally division by y(1+y) gives r_{0,F} as an alternating sum of the coefficients [y^E]A_2 for E ≤ F+1, proving degree at most 4F+4. Exact Newton interpolation of degree 4F+4 therefore needs 4F+5 points; the existing 4F+13 points suffice. This degree argument and the interpolation are ordinary mathematics, not yet a formal Lean certificate. The interpolation gives (scripts/certificate_342364.py, logs/certificate-342364.log, ALL_OK true):

* m = 4t+3: nu2(r_{0,1}) >= 7 and nu2(r_{0,2}) >= 7 for all t (every binomial-basis coefficient has nu2 >= 7).
* m = 16t+15: nu2(r_{0,1}) >= 11 and nu2(r_{0,2}) >= 11.
* m = 16t+11: nu2(r_{0,1}) = 7 exactly (b_0 has nu2 = 7, all b_i with i >= 1 have nu2 >= 8).

**Per-monomial gains.** Lemma W's proof shows that a monomial R_E y^E contributes to T~ with weight gain >= 1 if E is odd, >= 2 if E >= 2 is even, and >= min(1 + nu2(m+1), 2) = 2 if E = 0 (m odd).

*Part 2, m ≡ 1 (mod 4).* nu2(r_{0,0}) = 1 + nu2(m+1) + nu2(m+5) = 3. By (2), ω(r_0) >= 3, and nu2(r_{0,F}) >= 5 for F >= 1. Lemma W gives ω(r_j) >= 3 + j, which yields the lower bound. The readout at j = 0 gives equality for every odd n.

*Part 3, m ≡ 3 (mod 4).*
* j = 0: nu2(r_{0,0}) = 3 + max(nu2(m+1), nu2(m+5)) >= 6; nu2(r_{0,1}), nu2(r_{0,2}) >= 7; and r_{0,F} >= 2F+3 >= 9 for F >= 3. So r_0 ∈ 2^6 Z[y].
* j = 1: the monomial weights of r_0 are >= 6 (E=0), >= 6 (E=1), >= 5 (E=2), and >= 2E+3-bitlen(E) >= 7 (E >= 3). With the per-monomial gains in Lemma W, ω(r_1) >= 7, and Lemma W gives ω(r_j) >= 6 + j for j >= 1. This is the lower bound nu2(n) + 6.
* Equality, m ≡ 3 or 7 (mod 16): nu2(r_{0,0}) = 6, and the other coefficients have nu2 >= 7. The readout gives equality at every odd n.
* Equality, m ≡ 11 (mod 16): r_{1,0} = 2(m+1) r_{0,0} + r_{0,1}. The first summand has nu2 >= 10 and the second exactly 7, so nu2(r_{1,0}) = 7. The other coefficients of r_1 have nu2 >= 7 + bitlen(F) >= 8. The readout gives equality at every n = 2o with o odd.
* m ≡ 15 (mod 16): nu2(r_{0,0}) = 3 + nu2(m+1) >= 7; r_{0,1}, r_{0,2} have nu2 >= 8 (the stronger >= 11 is unnecessary); and r_{0,F} >= 9 for F >= 3. So r_0 ∈ 2^7 Z[y]. The monomial weights are >= 7, 7, 6 and >= 7 (E >= 3), so ω(r_1) >= 8 and ω(r_j) >= 7 + j. Hence nu2(c_m(4n) - c_m(n)) >= nu2(n) + 7 for all n, and the bound nu2(n) + 6 is never an equality. ∎

## 6. Checks performed (all exact integer arithmetic, capped single processes)

* logs/crossval-m{2,3,6,15}.log: C^m d_j reproduces c_m(2^j·4n) - c_m(2^j n) exactly for n <= 60, j <= 2, with c_m computed independently from the product definition.
* logs/reduced-m1-64-J6.log: Lemma R holds as an identity (r_{j+1} = T~(r_j)), and ω increases at each step, for m = 1..64, j < 6.
* logs/structure-check-64.log: the even-m (ρ) and odd-m (G, T') factorizations and the crude bound (2) hold for m = 1..64.
* logs/valscan-N4096-m1-64.log: brute-force valuations for m = 1..64, n <= 4096 (mod 2^64). There are no violations of parts 1–3. The minimum excess over the conjectured constant is 0 except for m = 15, 31, 47, 63, where it is 1, 2, 1, 3. Equality positions match the theorem.
* logs/valuation-beyond-n.log (inherited, hash-verified): m = 11..16, n <= 150000; m = 15 never attains the excess 0.

## 7. Novelty and prior-art status (as of 2026-11-03)

* arXiv:1904.03398 has only v1. The published Ramanujan J. version (fetched snippet in outputs/web-search-2.json) keeps Conjecture 6.1 verbatim.
* OpenAlex lists two citing works (sources/openalex-cites-W2930810148.json): Sobolewski 2023 (k-regularity of valuation sequences) and Żmija 2023 (Acta Math. Hungar., colored p-ary partitions with k(p-1) colours, which is a different function). Both abstracts were read, and neither addresses c_m(4n) - c_m(n). The Semantic Scholar citation API returned 429 and was not retried.
* Web searches (standard and extended, 2026-11-03) found no resolution.
* Omega D5/Problems trees at d5f7c3fd (fetched 2026-11-03 ~11:15 UTC by the cancelled worker; hash-verified) and the OpenAI/math tree and preprints at 4eaee875 contain no entry on this conjecture. The Ulas-related Omega entries concern other conjectures (Gawron–Ulas factorial sign, Miska–Ulas sigma, Sobolewski–Ulas Hankel and meta-Fibonacci).
* Prior campaign notes: the ID only matches numeric data in unrelated files. No coverage was found.

Caveats for root:
1. The parity of the m = 2^s - 1 colour counts is known to be special in related work (Gawron–Miska–Ulas for b_m). This explains the phenomenon but does not resolve this conjecture.
2. The refutation part concerns the sharpness clause. The positive parts (the even equality for all k and both inequalities) are new full proofs of the remaining clauses.
3. Section 5 uses interpolation certificates for three coefficient families. The degree bound deg_m r_{0,F} <= 4F+4 is argued from the τ-expansion; a degree-(4F+4) Newton fit agreeing on 4F+13 >= 4F+5 points therefore equals the true polynomial. A Lean version would instead prove these valuation facts symbolically or via the binomial-basis identity.

## Round 1 formal boundary

The six components of `Ulas.Remaining` are open, not assumptions silently added to the environment. `full_theorem`, `mathdb_342364`, and `conj61_some` each explicitly take this Prop as an argument. The coefficient polynomial identities, operator identity, weight lemma and arithmetic invariant remain to be proved.

## Round 2 formal boundary

New checked modules: UlasOperator, UlasParity, UlasLow, UlasFinal2. All four round-1 modules are frozen and included without changes.

- `C_functional` proves F1 for the actual stabilized product by first proving the finite identity `G (N+1) = w * expand 2 (G N)` and using coefficient agreement.
- `even_odd_decomposition` splits any integer power series into expanded even and odd sections. This proves `sectionEven_mul_expand` without division by two or summation reindexing.
- `sectionEven_C_pow_mul` proves F2 for arbitrary integer series F. This is the full-series identity, not yet its polynomial-in-y specialization.
- `c_transfer` and `Round2.diff_readout` prove equation (1) for arbitrary m, j, n. The numerators `transferIter` and `transferDiff` are currently full power series. No finite polynomial representation or divisibility by y(1+y) has been proved.
- `C_mod_two` and `C_pow_mod_two` prove F4. After reduction to ZMod 2, w is one and the functional equation is f = expand 2 f. Strong induction on the index forces every positive coefficient to vanish.
- `q_pow_low` proves all coefficients through degree four for every m by induction on m and convolution with q. `diff_one_polynomial` gives the exact integer identity 3 diff(m,1) = 2m²(m+1)(m+5). This is not a proof of the reduced constant coefficient until the polynomial bridge is established.

Still unformalized: Lemma R and the polynomial y representation, Chebyshev identities and Kummer estimates, bit-length Lemma W, readout of exact valuations, general strict growth, and the reduced low coefficients r_(0,1), r_(0,2). The existing conditional endpoints remain explicitly conditional in namespace Ulas.Round2. There is no unconditional endpoint in this packet.

ROOT RULING: the equality Props remain sufficient sets. No iff equality-set claim is needed or introduced. For m = 15 mod 16, the stronger universal bound remains the exact open obligation.


## Round 3 formal boundary

UlasWeight defines Weighted v R by 2^(v + Nat.size E) dividing every coefficient R_E. This correctly handles zero coefficients and gives a natural-number formulation of the ordinary weight bound. The checked size_add_le includes zero arguments. The checked reducedTerm has exponent 2i+1 for even E and 2i for odd E, exactly matching the displayed binomial formulas.

weighted_reduced proves the one-step gain; weighted_reducedIter proves the gain after any number of applications. weighted_reducedTail proves the stronger gain of two after removing the i=0 odd terms and the E=i=0 term. reduced_main_tail is the exact splitting into that leading finite sum and the tail. coeff_reduced_zero proves the exact constant coefficient 2(m+1)R_0+R_1. The current leading-part definition is a finite sum with the same support and cutoffs as reduced, rather than a canonical compressed polynomial.

The construction is an integral polynomial by definition; this does not establish that the actual series operator preserves polynomials in y. Lemma R's series bridge is still absent. The Chebyshev/Kummer initialization, even invariant, odd half-angle initialization, low-coefficient identities for reduced r_(0,1) and r_(0,2), exact valuation readout and general nonzero differences are also not proved. The universal n=1 polynomial from round 2 is retained and is not misidentified with a reduced coefficient identity.

All six residual Props remain open, and all full endpoints are conditional. mathdb_of_fifteen isolates the sole sufficient premise for the per-k refutation, without supplying it. This is a proof-engineering observation and not a resolution. The integrality repair, degree bound 4F+4 with 4F+5 interpolation points, per-monomial citation and the sufficient >=8 repair at the fifteen-family step are retained from the corrected round-2 ordinary proof. Historical computation and prior-art claims above refer to the upstream lanes, not new round-3 searches.
