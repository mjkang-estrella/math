# A first-order reflection argument for Guo’s Conjecture 6.2

Stage-3 manuscript. The literal rational-function statement of Guo’s Conjecture 6.2 is proved in Lean as `Guo62.guo_conj_6_2`, under exactly m>0, n>1 and n≡1 (mod 4). The axioms are only propext, Classical.choice and Quot.sound. REPORT.md records compilation, independent kernel checking and fresh replay of the printed sources.

## Source definitions, quoted and transcribed

Guo, arXiv:2310.15207v1, p.2: “The q-shifted factorial is defined by”
\((a;q)_n=(1-a)(1-aq)\cdots(1-aq^{n-1})\) for \(n\ge1\), \((a;q)_0=1\).
“Furthermore, the q-integer is defined as” \([n]_q=(1-q^n)/(1-q)\).
The source’s rising factorial is \((a)_n=a(a+1)\cdots(a+n-1)\) (p.1).
Its congruence definition (p.2) requires the numerator of the reduced fraction of the difference to be divisible by the modulus in \(\mathbb Z[q]\).

The literal Lean objects are `poch a d k = ∏ j ∈ range k, (1-q^(a+d*j))`, `qInt2 n = ∑ i ∈ range n, q^(2*i)`, and `halfPoch k = ∏ j ∈ range k, ((1:ℚ)/2+j)`; `q` is exactly `RatFunc.X`. The theorem `qInt2_eq_fraction` proves the geometric-sum bridge between the two q-integer forms in Lean. `CongSq` retains both regularity conditions required by the review, as well as square divisibility of the reduced numerator over ℚ. The source’s integral-numerator convention follows from the rational statement by Gauss’s lemma. Write a reduced difference as A/B with A,B in ℚ[q], and clear scalar denominators and content in A to obtain a primitive integral numerator A₀. Divisibility of A by the monic integral polynomial Φ_n² over ℚ implies divisibility of A₀ over ℤ by Gauss’s lemma; scalar normalization does not change the cyclotomic multiplicity. For a zero difference the numerator is zero under either convention. This elementary comparison is not a Lean declaration in this packet. The source defines congruence through the reduced numerator of the difference; `CongSq` additionally proves regularity of each side separately. These extra conjuncts strengthen rather than weaken the source assertion.

The corresponding literal Lean definitions are:

```lean
abbrev q : RatFunc ℚ := RatFunc.X

def poch (a d k : ℕ) : RatFunc ℚ :=
  ∏ j ∈ Finset.range k, (1 - q^(a + d*j))
def qInt2 (n : ℕ) : RatFunc ℚ := ∑ i ∈ Finset.range n, q^(2*i)
def halfPoch (k : ℕ) : ℚ := ∏ j ∈ Finset.range k, ((1:ℚ)/2 + j)
def CongSq (n : ℕ) (f g : RatFunc ℚ) : Prop :=
  IsCoprime (cyclotomic n ℚ) f.denom ∧ IsCoprime (cyclotomic n ℚ) g.denom ∧
  (cyclotomic n ℚ)^2 ∣ (f - g).num

def lhs (m n : ℕ) : RatFunc ℚ :=
  ∑ k ∈ Finset.range (m*n),
    (1 + q^(4*k+1)) * (poch 2 4 k)^3 * q^k / ((1 + q) * (poch 4 4 k)^3)
def rhs (m n : ℕ) : RatFunc ℚ :=
  qInt2 n * poch 3 4 ((n-1)/2) / poch 5 4 ((n-1)/2) * (q^((n-1)/2))⁻¹ *
    ((∑ k ∈ Finset.range m, (halfPoch k)^3 / (Nat.factorial k : ℚ)^3 : ℚ) : RatFunc ℚ)
```

The definitions above paraphrase the surrounding prose and reproduce its mathematical formulas; the exact source transcription is cached in the proof lane’s sources/2310.15207.txt, pp.1–2. The conjecture below is transcribed from p.15. No publication or novelty beyond the review is claimed.

# 360458 — a first-order reflection proof of Guo's Conjecture 6.2

A complete written proof and Lean certificate accompany this manuscript. A bounded prior-art search is recorded in PRIOR-ART.md. Significance and priority require independent adjudication; neither publication priority nor first-tier acceptance is asserted here.

## Source and literal statement

Victor J. W. Guo, *Dwork-type q-congruences through the q-Lucas theorem*, arXiv:2310.15207v1, §6, Conjecture 6.2, (6.6), p.15. The 2025 version of record, DOI 10.1007/s13398-025-01762-9, retains Conjecture 6.2 and the same statement.

> Let m and n be positive integers with n ≡ 1 (mod 4) and n > 1. Then, modulo Φ_n(q)^2,

\[
 \sum_{k=0}^{mn-1}
 \frac{(1+q^{4k+1})(q^2;q^4)_k^3}{(1+q)(q^4;q^4)_k^3}q^k
 \equiv
 \frac{[n]_{q^2}(q^3;q^4)_{(n-1)/2}}{(q^5;q^4)_{(n-1)/2}}
 q^{(1-n)/2}\sum_{j=0}^{m-1}\frac{(1/2)_j^3}{j!^3}.
\]

This is exactly the theorem proved below, for all such m,n, including composite n. Congruence of rational functions means the difference has numerator divisible by the indicated polynomial after reducing the fraction, and its denominator is coprime to that polynomial. The apparent singularities in the displayed summands must be cancelled before evaluation.

## 1. Notation and a stronger block identity

Put
\[
 R_k(q)=\prod_{j=1}^{k}\frac{1-q^{4j-2}}{1-q^{4j}},\qquad
 t_k(q)=\frac{1+q^{4k+1}}{1+q}q^k R_k(q)^3,
 \qquad c_l=\frac{\binom{2l}{l}}{4^l}=\frac{(1/2)_l}{l!}.
\]
Empty products are 1. We prove the block identity
\[
 \boxed{\quad
 \sum_{s=0}^{n-1}t_{ln+s}(q)
 \equiv c_l^3\sum_{s=0}^{n-1}t_s(q)\pmod{\Phi_n(q)^2}
 \quad} \tag{B}
\]
for every integer l≥0 and every n>1 with n≡1 (mod 4).

Throughout §§2–5, fix an arbitrary primitive nth root ζ. Set
\[
 h=(n-1)/2,\quad Q=\zeta^4,\quad
 f(x)=\frac{x}{1-x},\quad
 H=\sum_{j=1}^{h} f(Q^j),\quad C=-n^2-4nH.
\]
Here h is even and Q has order n. Every nonsingular factor used below is nonzero; quotients with removable singularities are interpreted through the cancelled representatives in §2: Q^j≠1 for 1≤j<n, and a power of an odd-order root cannot equal −1. We write D=q(d/dq), and apply D only to rational functions regular at ζ. A logarithmic derivative of a nonzero function F means (DF)(ζ)/F(ζ); no choice of logarithm is involved.

## 2. Regularity, valuations, and the whole-block core

In R_{ln+s}, for 0≤s<n, the numerator factors vanishing at ζ occur at indices j≡(n+1)/2 (mod n); the denominator factors occur at j≡0 (mod n). Consequently the numbers of such factors are l+1_{s>h} and l. Each factor has a simple zero. Thus R_{ln+s} is regular, and t_{ln+s} vanishes to order at least 3 when s>h. These tail terms contribute neither a value nor a first derivative.

For the core R_{ln}, match its l vanishing numerator factors, of exponents 2n(2u+1), with its l vanishing denominator factors, of exponents 4n(u+1), for 0≤u<l. For positive multiples a,b of n,
\[
 \left.\frac{1-q^a}{1-q^b}\right|_{q=\zeta}=\frac ab,
 \qquad
 D\log\frac{1-q^a}{1-q^b}\bigg|_{q=\zeta}=\frac{a-b}{2}. \tag{1}
\]
For example, substitute q=ζ(1+ε) and divide the expansions through order ε². Each matched pair therefore contributes (2u+1)/(2u+2) to the value and −n to the logarithmic derivative.

The other factors in each n-term block have the same nonzero residues in numerator and denominator, each once. Their values cancel. Their logarithmic-derivative contribution is independent of the block number, since adding 4un to all exponents contributes equal opposite sums. It follows that
\[
 R_{ln}(\zeta)=c_l,\qquad
 D R_{ln}(\zeta)=lc_l C. \tag{2}
\]
Here is the calculation of C, rather than an appeal to a q-Lucas derivative formula. For a single block its nonsingular part gives
\[
 C=-n+\sum_{j=1}^{n-1}4j f(Q^j)
       -\sum_{\substack{0\le j<n\\j\ne h}}(4j+2)f(\zeta^{4j+2}).
\]
For j<h, put r=j+h+1, so 4j+2=4r−2n and h<r<n. For j>h, put r=j−h, so 4j+2=4r+2n and 1≤r≤h. Thus
\[
 C=-n+2n\left(\sum_{r=h+1}^{n-1}f(Q^r)-\sum_{r=1}^{h}f(Q^r)\right).
\]
Since f(x^{-1})=−1−f(x), the first sum equals −h−H. This gives C=−n−2nh−4nH=−n²−4nH, as claimed.

## 3. The first-order shift error

For 0≤s≤h define
\[
 H_s=\sum_{j=1}^{s}\left(f(Q^j)-f(\zeta^{4j-2})\right),
 \quad
 w_s=\frac{\zeta^{4s+1}}{1+\zeta^{4s+1}},
 \quad L_s=w_s+3H_s.
\]
The factors added to R_{ln} to reach R_{ln+s} have value R_s(ζ). Their logarithmic derivative differs from that of R_s by 4ln H_s: this follows termwise from
\[
 D\log(1-q^a)\big|_\zeta=-a\frac{\zeta^a}{1-\zeta^a}
\]
and replacing a by a+4ln. Combining this with (2), and differentiating the elementary prefactor in t_k, gives
\[
 t_{ln+s}(\zeta)=c_l^3t_s(\zeta), \tag{3}
\]
\[
 D t_{ln+s}(\zeta)
 =c_l^3\left(Dt_s(\zeta)
   +l\,t_s(\zeta)\,[3C+n+4nL_s]\right). \tag{4}
\]
All functions divided by here are nonzero for s≤h. The extra n in (4) comes from q^{ln}; the extra 4nw_s comes from 1+q^{4ln+4s+1}; and the extra 12nH_s comes from R^3. These account for every factor.

## 4. Reflection cancels the entire error

The crucial identities are
\[
 t_{h-s}(\zeta)=t_s(\zeta),\qquad
 L_s+L_{h-s}=1+3h+6H. \tag{5}
\]
Here are explicit proofs.

First, ζ²=Q^{−h}. Reversing finite products in
\(R_s(\zeta)=(Q^{-h};Q)_s/(Q;Q)_s\) gives
\[
 \frac{R_{h-s}(\zeta)}{R_s(\zeta)}
 =(-1)^h Q^{(h+1)s-h(h+1)/2}. \tag{6}
\]
One can also verify (6) by writing
\((Q^{-h};Q)_s=(-1)^sQ^{-hs+s(s-1)/2}(Q;Q)_h/(Q;Q)_{h-s}\).
Since ζQ^h=ζ^{−1}, the ratio of the remaining prefactors in t_{h-s} and t_s is ζ^{h−1−6s}. After cubing (6), the total ratio is
\[
 (-1)^h\zeta^{h-1-6h(h+1)}
 =(-1)^h\zeta^{-n(3n-1)/2}=1.
\]
The last equality uses even h and ζ^n=1. This proves the first identity in (5).

For the second, ζ^{4j−2}=Q^{−(h+1−j)}, so
\[
 H_s=s+\sum_{j=1}^{s}f(Q^j)+\sum_{j=h+1-s}^{h}f(Q^j).
\]
Adding the expression with s replaced by h−s yields H_s+H_{h-s}=h+2H. Moreover ζ^{4(h-s)+1}=(ζ^{4s+1})^{−1}, whence w_s+w_{h-s}=1. This proves (5).

Write T=∑_{s=0}^h t_s(ζ). Reindexing this finite sum by s↦h−s and using (5),
\[
 \sum_{s=0}^{h}t_s(\zeta)L_s
 =\frac{1+3h+6H}{2}\,T. \tag{7}
\]
No division by T is made. In particular this is valid even if T=0. Since
\[
 3C+n+2n(1+3h+6H)=0, \tag{8}
\]
summing (4) proves equality of the first derivatives of the two sides of (B) at ζ. Equation (3) proves equality of their values. The terms s>h were dealt with in §2.

These equalities hold at every primitive nth root, and both sides are rational functions over ℚ regular at these roots. Clearing their reduced denominators therefore shows that the numerator of their difference is divisible by Φ_n². Indeed Φ_n is separable in characteristic zero, and the value and first derivative vanish at each of its roots. This proves (B).

## 5. The base block, with a finite certificate

The source's equation (4.1), originally Guo–Zudilin (2020), already supplies
\[
 \sum_{k=0}^{n-1}t_k(q)
 \equiv \frac{[n]_{q^2}(q^3;q^4)_h}{(q^5;q^4)_h}q^{-h}
 \pmod{\Phi_n(q)^2}. \tag{9}
\]
The tail terms above h have order at least 3. To keep the proof self-contained and give a realistic Lean route, the following finite telescoping proof establishes (9) without treating a published identity as an axiom.

For any integer N≥0 define, for 0≤k≤N,
\[
 u_{N,k}=
 \frac{1+q^{4k+1}}{1+q}q^k
 \frac{(q^2,q^{-4N},q^{4N+4};q^4)_k}
 {(q^4,q^{2-4N},q^{4N+6};q^4)_k}.
\]
Then the exact rational identity is
\[
 \sum_{k=0}^{N}u_{N,k}
 =q^{-N}\frac{1-q^{4N+2}}{1-q^2}
       \frac{(q^3;q^4)_N}{(q^5;q^4)_N}. \tag{10}
\]
At N=0 both sides are 1. For N≥1 put a=q², W=q^{4N}, X=q^{4k}, and
\[
 r_N=q^{-1}\frac{1-aW}{1-W/a}\frac{1-W/q}{1-qW},\qquad
 \mathcal R(X)=\frac{1+W}{qW-1}
 \frac{(1-X)(1-aWX)}{(1+qX)(1-WX)}.
\]
Extend u_{N,k} to k=N+1 and u_{N−1,k} to k=N by the same finite-product formulas; their terminating numerator factors make these boundary terms zero. For 0≤k≤N, direct cancellation of consecutive products gives
\[
 \frac{u_{N,k+1}}{u_{N,k}}
 =\mathcal T(X):=
 q\frac{1+q^5X}{1+qX}
 \frac{(1-aX)(1-X/W)(1-q^4WX)}
 {(1-q^4X)(1-aX/W)(1-aq^4WX)},
\]
\[
 r_N\frac{u_{N-1,k}}{u_{N,k}}
 =\mathcal V(X):=
 \frac{q-W}{1-qW}
 \frac{(1-X/W)(1-aWX)}{(1-WX)(1-aX/W)}.
\]
The rational certificate is
\[
 \mathcal T(X)\mathcal R(q^4X)-\mathcal R(X)
 =1-\mathcal V(X). \tag{11}
\]
It follows by substituting a=q², clearing denominators, and expanding; it is a polynomial identity in q,W,X. A separate exact symbolic verification is provided in `t1-pool029-proof-sol61-20261120-r1/scripts/check_dixon_certificate.py` (relative to the campaign directory); the final-check lane independently verifies the identity in `audit_aux.py`.

Multiplying (11) by u_{N,k} and summing k=0,…,N telescopes. Set u_{N,N+1}=0 and u_{N-1,N}=0, as their terminating numerator factors prescribe. The lower boundary vanishes since \(\mathcal R(1)=0\); the upper boundary vanishes since u_{N,N+1}=0. All rational factors at these boundaries are defined as elements of ℚ(q), since N≥1. Thus the sums satisfy F_N=r_N F_{N-1}. The right side of (10) has exactly the same consecutive ratio r_N. This proves (10) by induction.

Now take N=h=(n−1)/2. In u_{h,k} the two altered numerator parameters are q^{2−2n},q^{2+2n}, and the altered denominator parameters are q^{4−2n},q^{4+2n}. For every integer b,
\[
 (1-q^{b-2n})(1-q^{b+2n})-(1-q^b)^2
 =-q^{b-2n}(1-q^{2n})^2.
\]
Consequently u_{h,k}≡t_k modulo Φ_n² for 0≤k≤h. All relevant denominators are units at primitive nth roots, since their residues are 4,8,…,4h, none divisible by n. Applying (10) gives precisely (9), with [n]_{q²}=(1-q^{2n})/(1-q²).

On the right of (9), (q^5;q^4)_h contains exactly one factor 1−q^n: its exponent ranges from 5 to 2n−1 and n≡1 (mod 4). Cancel it with 1−q^{2n}, obtaining the regular factor 1+q^n. No other denominator factor vanishes at a primitive nth root. Thus the regularity assertion used in (9) is justified on both sides.

## 6. Finish the full conjecture

Split k=0,…,mn−1 into the m consecutive n-term blocks. By (B) and (9),
\[
 \sum_{k=0}^{mn-1}t_k(q)
 \equiv\left(\sum_{l=0}^{m-1}c_l^3\right)
 \frac{[n]_{q^2}(q^3;q^4)_h}{(q^5;q^4)_h}q^{-h}
 \pmod{\Phi_n(q)^2}.
\]
Since c_l³=(1/2)_l³/l!³, this is the source's exact statement. The admissible n begin at 5; l=0 was included throughout, and m=1 is the proved base block. No primality hypothesis or unstated size restriction was used. ∎


## Exact reciprocity behind the new error average

There is an exact invariant explaining why the first-order pairing works. This is an alternative proof of (7), not an additional counted result. Fix ζ,Q,h as above, let u be an independent indeterminate, and put
\[
 r_s(u)=\frac{(uQ^{-h};Q)_s}{(uQ;Q)_s},\qquad
 v_s(u)=\frac{1+u\zeta Q^s}{1+\zeta}\zeta^s r_s(u)^3,
 \qquad F(u)=\sum_{s=0}^h v_s(u).
\]
Reversing the last s factors of r_h gives the exact rational identity
\[
 r_{h-s}(u)=r_h(u)Q^{(h+1)s}r_s(u^{-1}).
\]
Indeed the factor indexed by j=h+1−r in the reversed quotient is
\[
 \frac{1-uQ^{h+1-r}}{1-uQ^{-r}}
 =Q^{h+1}\frac{1-u^{-1}Q^{r-h-1}}{1-u^{-1}Q^r}.
\]
The elementary plus-weight factor simultaneously transforms by
\[
 \frac{\zeta^{h-s}(1+u\zeta Q^{h-s})}
 {\zeta^s(1+u^{-1}\zeta Q^s)}
 =u\zeta^{h-1-2s}Q^{-s}.
\]
As Q^{h+1}=ζ², cubing the first factor cancels every s-dependent power in the second. Thus
\[
 \boxed{\quad F(u)=P(u)F(u^{-1}),\qquad
 P(u)=u\zeta^{h-1}r_h(u)^3.\quad} \tag{R}
\]
All these are rational identities in u, not equalities holding only at u=1. At u=1, P(1)=1 by the same parity calculation as (6). Also r_h'(1)/r_h(1)=H_h=h+2H, hence P'(1)=1+3h+6H. Legitimately differentiating (R) at 1 yields
\[
 2F'(1)=(1+3h+6H)F(1),
\]
which is (7), since v_s(1)=t_s(ζ) and v_s'(1)=t_s(ζ)L_s.

This exact reciprocity distinguishes the argument from erroneously differentiating a congruence valid only at roots. It also explains the residue-class distinction: for n≡3 (mod4), the analogous P(1) is −1, so the same identity forces F(1)=0 but gives no first-derivative constraint. The arbitrary-m vanishing theorem in that other class does not itself supply the positive-eigenvalue derivative identity needed here.


## Prior work and significance

The source proves block values modulo Φ_n, and Guo–Zudilin (2020) proves the base case m=1. Guo’s earlier arbitrary-m theorem concerns n≡3 mod4 and a vanishing right side. The proposed additional step here is the first-order complementary shift error, or equivalently the exact shift-parameter reciprocity. It does not follow by differentiating an identity that holds only at roots.

The independent Opus review describes this as provisional and borderline on routine: all tools are standard, and a specialist may view it as a natural extension of the q-Lucas argument. Liu–Tao, arXiv:2606.12037 (10 June 2026), proves two different conjectures, not this Conjecture 6.2. Its first theorem is itself a square-cyclotomic congruence, combining a known square-modulus auxiliary result with rootwise reflection; its second theorem uses period decomposition and value-level reflection modulo [n]. Thus “value-level” describes the shared reflection/block mechanism, not the maximum modulus in that paper. Neither theorem states the arbitrary-m first-order block lift proved here. The review found no exact resolution in its bounded source/citer/registry screen. ProbXiv was unavailable (HTTP402), and some recursive registry trees were truncated; no exhaustive priority clearance is asserted. No companion Conjecture 6.1 or stronger block identity is counted independently.

## Formal statement fidelity

The theorem has only the review’s m,n, positivity, n>1 and n%4=1 hypotheses. All displayed denominators are proved nonzero as rational functions separately from cyclotomic regularity. The latter is proved after the singular factors are paired and removed. The source’s base case is also proved within the packet by finite Dixon; it is not a theorem assumed from the literature. REPORT.md prints the complete literal endpoint and its axioms.

## Checked implementation map

`GuoStatement` fixes the source objects and proves all endpoint divisions are by nonzero elements of ℚ(q). `GuoCongruence` proves equivalence with polynomial witnesses having cyclotomic-unit denominators. `GuoRoots` replaces enumeration of all primitive roots by the minimal-polynomial criterion at one genuine primitive root, and proves the formal-derivative square factor criterion. This is shorter than the paper’s root-enumeration argument.

`GuoReciprocity` proves the exact identity (R) over a field under its explicit nonzero factor hypotheses; its prefactor is written u·(ζ^h/ζ)·r_h(u)^3. For h≥1 this is the displayed u·ζ^{h−1}·r_h(u)^3. The module proves the ratio reflection first, then the weighted terms, then the finite sum. The root-order consequences and regularity of reversed factors at u=1 are proved in `GuoRoots`; the identity P(1)=1 and the concrete reflected-error specialization are now proved in GuoReciprocityAtOne, as described below.

`GuoGeometric` proves (1) with exponents a=nA,b=nB using the faithful polynomial representatives G_A(q)=∑_{j<A}q^{nj} and G_B(q). At ζ they have values A and B, and their logarithmic Euler derivatives differ by n(A−B)/2. The denominator G_B is coprime to Φ_n because its value B is nonzero in characteristic zero. No zero denominator is evaluated. `GuoAlgebra` retains the original proof lane’s checked algebraic helpers with narrow imports; `GuoFirstOrder` specializes the weighted cancellation to [0,h] and proves the conditional derivative assembly. Neither module computes derivatives of the original long products.

The finite q-Dixon certificate, its rational identity, induction, boundary terms and base specialization are all proved in Lean. The block congruence is integrated with a faithful polynomial-fraction jet interface, and the finite sum over blocks yields the literal endpoint. No source-specific proof obligation remains.


## Formal implementation of the cancelled core

The formal core uses polynomial witnesses rather than a limit of the displayed singular quotient. Put n=2h+1 and, in the block numbered u, split the numerator at its zero factor j=h and the denominator at its last factor j=n. The zero pair is represented by geomPoly(n,4u+2)/geomPoly(n,4u+4). Of the remaining factors, j<h maps to residue r=h+1+j, and j>h maps to r=j-h. These are bijections onto the upper and lower nonzero halves respectively. The exponent differences from the paired denominator are -2n and +2n. All denominators in this representative have nonzero evaluation at every primitive root, including for composite n.

For a polynomial P with P(z) nonzero, define E_z(P)=z P'(z)/P(z). The formal proof establishes E_z(product P_i)=sum E_z(P_i) by induction on the finite set of factors, using the polynomial product rule only once in the inductive step. Applying this to the cancelled block gives -n+2n(U-H), where U is the upper harmonic half. Reversal r -> n-r and f(x^{-1})=-1-f(x) give U=-h-H, hence -n²-4nH. Applying the same finite-product lemma over u=0,...,l-1 yields l times this constant. The value product is identified in Lean with the source's literal halfPoch(l)/l!, by its elementary consecutive ratio, not with an unproved binomial normalization.

`core_fraction_identity` connects these polynomial witnesses to the actual rational-function Pochhammer ratio. `core_euler_derivative` proves the quotient cross-derivative formula l*c_l*C. `fraction_cross_derivative_zero` connects equality of quotient values and these Euler derivatives to vanishing of a polynomial cross numerator and its derivative, so that the previously checked cyclotomic-square criterion applies. Thus there is no unformalized model-equivalence step in the uniform core calculation.

For P(1)=1 in the exact reciprocity, even h gives the fixed index s=h/2. Its individual summand is nonzero, since all its factors are units at the root. Termwise reciprocity at this index forces P(1)=1. This cancels a single nonzero term and never divides by the complete block sum. This is an alternative to the exponent-parity computation in the written proof above. These specializations and the final source endpoint are proved in the printed Lean certificate. REPORT.md records their verification.


## Stage-3 integration and finite identity

For a rational function f, `HasJet z f v d` supplies polynomials A,B with f=A/B, B(z)≠0, A(z)=v B(z), and z A′(z)=d B(z)+v z B′(z). Thus v and d are the actual value and Euler derivative of a regular representative. The interface is closed under finite sums and products, and under inverses with nonzero value. Equality of two such jets makes their cross numerator and its derivative vanish; the minimal-polynomial and separability lemmas then imply the exact reduced-numerator square congruence, including both regularity conditions.

`base_term_value_bridge` identifies the literal base witness with the specialized shift term. Summing the inherited derivative formula now gives `block_jet_values`; `source_block_lift` applies the multiplicity bridge; `source_all_blocks` partitions the full sum. These steps use no assumed summand-derivative or block-sum identities.

The finite Dixon implementation separates a parameter P(a,Q,k)=∏_{j<k}(1−aQ^j). Its consecutive-parameter identity P(aQ,Q,k)(1−a)=P(a,Q,k)(1−aQ^k) follows by induction. Four instances produce the N-to-N−1 term ratio. The k-to-k+1 ratio and the rational version of certificate (11) give the telescoping difference directly. The boundary values are proved from the terminating product factor and R(1)=0, with every denominator nonzero in ℚ(q). The closed expression has the same N recurrence, and the N=0 case is 1. This proves `finite_dixon_sum` for all N.

For the quadratic specialization, the two factors with exponents a−2n and a+2n have the same product value and Euler derivative as (1−q^a)² at a primitive root. The implementation proves this with `HasJet` also for negative exponents, then multiplies the pairs and divides only by factors of nonzero evaluated value. It follows that every relevant terminating summand and source summand has the same faithful first jet. Tail terms have zero first jet by the inherited cubic numerator proof. Finite Dixon therefore gives `source_base_block`. The RHS’s unique singular denominator factor is explicitly removed in `rhs_fraction`, and `source_rhs_regular` supplies its reduced-denominator regularity. Congruence addition and multiplication finish `guo_conj_6_2`.


## Prior-art assessment inherited from the independent review

The Opus review of 20 November 2026 records the following assessment (not a new search in this stage):

> By the q-Lucas theorem, Guo proves the analogous statements only **modulo Φ_n(q)** (Lemma 2.2 and Theorem 1.3 with r = 1 give the block values). He states the Φ_n² refinement as Conjecture 6.2.

> The n ≡ 3 (mod 4) analogue (6.5) was proved earlier by Guo for all m, using a Watson transformation and a vanishing right-hand side.

> The base case m = 1 is Guo–Zudilin 2020 (the source's (4.1)).

The review’s bounded public screen found the source’s 2025 journal version unchanged, three citing papers addressing other sums, and the related Liu–Tao 2026 reflection paper addressing different conjectures. Its six registry searches returned no entries. ProbXiv was unavailable; exhaustive clearance remains unclaimed. The review estimates a 0.55 probability that a specialist would regard the proof as nonroutine. Formal verification settles the stated algebraic theorem, not this significance judgment.


## Independent final check (20 November 2026)

The final-check reviewer compared the arXiv v1 statement and the previously cached journal full text against the literal endpoint; no mismatch was found. Independent exact arithmetic in ℚ(q), for every n in {5,9,13} and m in {1,2,3}, found both reduced denominators coprime to Φ_n and the reduced difference numerator divisible by Φ_n² but not Φ_n³ in all nine cases. The telescoping certificate was separately checked as an exact symbolic identity. All 39 appendix modules matched src/ byte for byte. These checks supplement the proof; the final-check reviewer did not compile Lean.

Fresh Semantic Scholar and OpenAlex citing lists identified the same three relevant citing papers already screened. Fresh omega issue and PR searches by source ID and “Dwork Lucas” returned no hits, as did two global GitHub code searches and focused searches of the four local archives. ProbXiv again returned HTTP 402 and was not bypassed. Guo’s 2026 *Three Dwork-type q-supercongruences from the q-Dixon sum* was located through its publisher abstract (which features −2/3 parameters); its full text was inaccessible in this refresh, so it is not presented as fully cleared. This remains bounded priority evidence. The final reviewer judges the specific first-order error coupling sufficient for the stated nonroutine criterion, while retaining the earlier borderline significance assessment.
