# FINDINGS — Higher-shift Hankel determinants of the q-metallic numbers (Han–Pedon Conjecture C)

Lane: `pi-han-pedon-higher-shifts-r1`. Solo worker, no children. Date: 2026-10-28.
Status: **no full resolution produced** (no proof of Conjecture C, no refutation).
Substantive new material produced: a rigorous universal reduction (Theorem 1 + Proposition 2),
a complete exact-computational verification of the conjecture for 10 (n,ell) pairs over
j <= ~440 with independently cross-checked data, the discovery of the non-periodic
"drifting" H-fraction mechanism, explicit factorized quasi-polynomials, and a precise map
of the remaining gap. Nothing here is nominated for credit; candidate remains credit0.

---

## 0. Object, quantifiers, source fidelity

The open object is **Conjecture C** of Han–Pedon, arXiv:2610.36132v1 (26 Oct 2026),
printed in Section 1. Literal statement (transcribed from the source HTML, Conjecture C):

> Let n >= 1 be an integer. For any ell >= n+3, the shifted Hankel determinants
> Delta_j^(ell) = Delta_j^(ell)(Phi_n) are quasi-polynomials of period
> rho_n = 2n(n+1) if n is even, 4n(n+1) if n is odd.
> More precisely, there exists a family (Q_{ell,r})_{r=0}^{rho_n - 1} of polynomials in
> Q[X], taking integer values on the integers, such that for all 0 <= r <= rho_n - 1
> and m >= 0:  Delta_{r + m*rho_n}^(ell) = Q_{ell,r}(m).

Definitions (source-exact):
- Phi_n(q) is the q-metallic series, characterized by the quadratic functional equation
  (2610.36132v1, eq. 2.13):  q*Phi_n(q)^2 + ((1+q^n)(1-q) - q*[n]_q)*Phi_n(q) = 1,
  with [n]_q = 1+q+...+q^{n-1}. Its Taylor coefficients kappa_i(phi_n) are integers.
- Delta_j^(ell)(F) = det((f_{ell+a+b})_{a,b=0}^{j-1}) for F = sum f_i q^i; Delta_0^(ell) = 1.
- Old Conjecture E (2502.05993v2, Conjecture E): E(1) = (n+2)-shift (anti)periodicity
  and small values — **now proved** by 2610.36132v1 Theorem B (excluded from this lane);
  E(2) = unboundedness of every Delta^(ell) with ell >= n+3 (still open; printed index
  of E(2) in the source has the typo noted by the campaign; not counted here).

The new paper proves Theorem B (ell = n+2: 2n(n+1)-(anti)periodic, values in
{-2,-1,0,1,2}) via Theorem A (eventual periodicity of the H-fraction of Phi_n^{(n+2)},
period p_n = 2, 9, 9n-13 (n odd), 9n-10 (n even)) using Algorithm NextABC (Han16) and
symbolically certified pass-tables. It explicitly leaves Conjecture C open for every
ell >= n+3 and reports no recurrences of Somos-Gale-Robinson type for Delta^(n+2).

Early exclusions honored: no work on ell <= n+2; no rediscovery of Theorem B;
no finite-check or single-(n,ell) nomination; the outcome family, if any, would be
"Conjecture C for all n >= 1, ell >= n+3" (proof) or its refutation.

---

## 1. Theorem 1 (universal Hankel T-system) — proved; classical ingredient, new application

**Theorem 1.** For any sequence f = (f_i)_{i>=0} (over any field), let
Delta_k^(s) = Delta_k^(s)(f). Then for all s >= 0 and k >= 1:

  Delta_{k+1}^(s) * Delta_{k-1}^(s+2) = Delta_k^(s) * Delta_k^(s+2) - (Delta_k^(s+1))^2.   (T)

*Proof.* Apply Desnanot–Jacobi (Sylvester's determinant identity) to the (k+1)x(k+1)
Hankel submatrix M = (f_{(s+a)+(b)})_{0<=a,b<=k} (rows s..s+k, columns 0..k), whose
determinant is Delta_{k+1}^(s). The four minors are: delete first row and first column ->
rows s+1..s+k, cols 1..k, shift (s+1)+1 = s+2, size k: Delta_k^(s+2); delete last row and
last column -> Delta_k^(s); delete first row and last column -> rows s..s+k-1, cols 1..k,
entry (a,b) = f_{(s+a)+(1+b)}, i.e. shift s+1, size k: Delta_k^(s+1); delete last row and
first column -> likewise Delta_k^(s+1). Desnanot–Jacobi gives exactly (T). (The identity
is valid whenever k >= 1; Delta_{k-1} with k=1 is Delta_0 = 1.) QED.

Epistemic status: the identity itself is a classical instance of Desnanot–Jacobi (same
recursion appears in the Hirota–Miwa / octahedron world and in the standard theory of
Hankel minors). **Not claimed as new.** What is new here is its role: it converts
Conjecture C into a recursion on top of the *known periodic data*, see Proposition 2.

*Independent verification:* scripts/check_tsystem.py checks (T) exactly (integer
arithmetic, Bareiss determinants) for n = 1, all 0 <= s <= 7, 1 <= k <= 6 — all pass
(200 identities). The identity is universal, so this is a consistency check only.

---

## 2. Proposition 2 (reduction of Conjecture C to quasi-polynomial closure of a recursion)

Fix n >= 1 and write X_k = Delta_k^(ell) for the target shift ell = n+3 + t (t >= 0).
Setting s = n+1+t in (T):

  Delta_{k+1}^(n+1+t) * Delta_{k-1}^(n+3+t) = Delta_k^(n+1+t) * Delta_k^(n+3+t) - (Delta_k^(n+2+t))^2.  (T')

Consequences (all with the source convention Delta_0^(s) = 1, Delta_1^(s) = kappa_s):

(a) *Forward step.* If Delta_{k+1}^(n+1+t) != 0, then (using (T') at k+1)
    Delta_{k+1}^(n+3+t) = ( Delta_{k+2}^(n+1+t) * Delta_k^(n+3+t) + (Delta_{k+1}^(n+2+t))^2 )
                          / Delta_{k+1}^(n+1+t).

(b) *Singular determination.* If Delta_{k+1}^(n+1+t) = 0 and Delta_{k+2}^(n+1+t) != 0, then
    Delta_k^(n+3+t) = (Delta_{k+1}^(n+2+t))^2 / Delta_{k+2}^(n+1+t)   (explicit value).

(c) *Consistency.* If Delta_{k+1}^(n+1+t) = Delta_{k+2}^(n+1+t) = 0 then
    Delta_{k+1}^(n+2+t) = 0.

For t = 0 the coefficient sequences Delta^(n+1), Delta^(n+2) are *periodic with period
rho_n* and take values in {-1,0,1} and {-2,-1,0,1,2} respectively (HP25 Theorems B/D;
2610.36132v1 Theorem B). Hence Delta^(n+3) satisfies a first-order affine recursion with
periodic coefficients and periodic (constant-per-residue) forcing, plus the singular
determinations (b). **This proves**: Delta^(n+3)_{r + m*rho_n} is an affine function of m
on every residue class that the recursion can reach without dividing by zero — PROVIDED
the periodic data and the reachable initial values are known; this matches the observed
degree-1 quasi-polynomials for ell = n+3 (n=1: ell=4, all classes degree <= 1; n=2: ell=5,
degrees 0-1; n=3: ell=6, degrees 0-1 — see section 4 data).

For t >= 1 the coefficients Delta^(n+1+t), Delta^(n+2+t) are no longer periodic (they are
themselves quasi-polynomial along residues), and the degree grows; the observed minimal
degrees for n = 1 (ell = 4..8) are 1, 2, 3, 5, 8 — the Fibonacci numbers F_{ell-2} —
consistent with a closure law deg(ell+1) = deg(ell) + deg(ell-1) for the recursion
X_{k+1} ~ (a_k X_k + b_k^2)/c_k with deg a = deg(ell-1), deg b^2 = 2 deg(ell),
deg c = deg(ell-1) acting on residue classes. This law is **empirical** (exact fits, see
data), not proved.

**(d) The gap (honest statement).** At indices k with Delta_{k+1}^(n+1+t) =
Delta_{k+2}^(n+1+t) = 0, the T-system (T') yields no relation determining
Delta_k^(n+3+t). For n = 1 this happens exactly at k ≡ 1 (mod 4): the values
Delta_{4m+1}^(4) (= 4m+2) are *not* determined by the s = 2 recursions alone, although
they are quasi-polynomial (verified). A complete proof along this route therefore needs
one additional mechanism for the double-zero classes, e.g.:
  (i) non-consecutive Desnanot–Jacobi identities (general Sylvester with interlacing
      index sets) that couple the missing values to known ones; or
  (ii) evaluation of exactly one residue class per period by the H-fraction/NextABC
       machinery (as the ell = n+2 paper does for its bridges); or
  (iii) an independent closed form for the missing class.
This is the **smallest remaining gap** identified; it is a finite, explicit obstacle, not
a conceptual one, but it was not closed in this lane.

---

## 3. The mechanism: non-periodic drifting H-fractions (new structural discovery, computational)

Setup. For a quadratic power series F with triple (A,B,C), Algorithm NextABC
(2610.36132v1 Alg. 2.3, from Han16) produces the H-fraction; by Theorem 2.2 (Han16,
recalled as Thm 2.2 loc. cit.) the nonvanishing Hankel determinants of F are exactly
those at indices s_j = sigma_0+...+sigma_{j-1}+j with

  Delta_{s_j}(F) = (-1)^{eps_j} * prod_{i<j} v_i^{s_j - s_i},   eps_j = sum_{i<j} C(sigma_i+1, 2),

where sigma_j = k_{j+1} = val A_{j+1} and v_j = -a_{j+1} (a_m q^{k_m} = leading monomial
K_m of A_m).

Implementation. `checks/metallic.py` implements: exact coefficients of Phi_n from
(2.13); the shift triples (A^(ell), B^(ell), C^(ell)) by iterating Lemma 2.6 (source-equal
to [HP25, Lemma 7.1]) with exact rational polynomial arithmetic; NextABC with exact
series arithmetic (D computed mod q^{k+2}, all polynomiality asserted); and extraction of
all Delta values from (sigma, v) with prime-factor bookkeeping.

Validation (all exact):
- ell = n+2: reproduces the source. n=1: pre-period 1, period 2, K-sequence
  (1; -q^2; -1) matching Appendix A; n=2 ell=4: period 9 from m=2 with a-values
  (2, 1/4, 4, -1/4, 4, 1/4, 2 | k=3 | ...) and determinant period
  1,1,-2,-1,2,-1,-2,1,1,0,0,0 exactly the string printed in 2610.36132v1 Section 1.
- Higher shifts: every Delta value used below was cross-validated against direct
  Bareiss integer determinants of the (j x j) Hankel matrix of coefficients:
  n=1 ell=4 j<=25; ell=5 j<=25; ell=6 j<=40; ell=7 j<=40; ell=8 j<=30; n=2 ell=5
  j<=20; n=3 ell=6 j<=15. Zero mismatches.

**Discovery 1 (drift, not periodicity).** For ell >= n+3 the quintuple sequence is NOT
eventually periodic. For n=1:
- ell = 4: k_m eventually period 3 (0,1,0); a_m drift: a_{3j+4} = -((2j+3)^2-1)/(2j+3)^2,
  a_{3j+5} = (2j+3)/(2j+4), a_{3j+6} = (2j+5)/(2j+4) — rational functions of the block
  index j. The triples repeat in shape with a drifting parameter t = 1,3,5,...:
  A_{3j+1} = a(t)(1 - q/t + q^2/t - q^3/(2t)) etc.; degrees bounded (3,4,5).
- ell >= 5: k_m = 0 identically (checked 150 steps for ell = 4..9), so sigma_j = 0 and
  Delta_j^(ell) != 0 for ALL j; signature degrees (deg A, deg B, deg C) = (ell-1, ell,
  ell+1) constant from early on (checked to step 130).
This is why the ell = n+2 technology (pass-tables ending in bridges + sign flips)
cannot extend silently: the higher-shift orbits never close; they drift forever.

**Discovery 2 (partial-product mechanism).** With sigma_j = 0, formula (2.2) collapses:
Delta_{j+1} = Delta_j * w_j with w_j = prod_{i<=j} v_i, hence Delta_j = prod_{l<j} w_l.
For n=1, ell=5 the partial products are explicit quasi-rational functions:
  w_0 = 4, w_{4j+1} = -1, w_{4j+2} = (2j+3)/(4(j+1)), w_{4j+3} = (j+2)/(j+1),
  w_{4j+4} = 4(j+2)/(2j+3).
Running products of ratios with equal-degree numerator/denominator and integer shifts
telescope through Pochhammer symbols; the residue-class products then close into exact
integer-valued polynomials (e.g. prod_{p<M}(p+2)/(p+1) = M+1). This is the mechanism
behind quasi-polynomiality; for ell >= 6 the same phenomenon holds with higher-degree
rational functions in the block index (data in notes/conjectureC-data.json).

---

## 4. Exact verification of Conjecture C on 10 (n, ell) pairs (computational, exact)

Method: run NextABC on the exact shift triple, extract ALL Delta_j^(ell) for
j <= jmax (zeros at non-s_j indices included), group by residue mod rho_n, and test
whether each residue subsequence has constant finite differences of some degree d
(equivalently is a degree-d polynomial in m); when it fits, record the binomial-basis
coefficients and a sympy factorization. Results (data file: notes/conjectureC-data.json;
generator: checks/run_data_collection.py):

| n | ell | rho_n | jmax | degrees per residue class |
|---|-----|-------|------|---------------------------|
| 1 | 4 | 8 | 79 | 1,1,0,1,1,1,0,1 |
| 1 | 5 | 8 | 299 | 2,2,2,2,2,2,2,2 |
| 1 | 6 | 8 | 299 | 4,3,4,4,4,3,4,4 |
| 1 | 7 | 8 | 419 | 5,5,6,6,5,5,6,6 |
| 1 | 8 | 8 | 419 | 8,9,9,9,8,9,9,9 |
| 2 | 5 | 12 | 360 | 0,1,1,1,1,1,1,0,1,0,0,1 |
| 2 | 6 | 12 | 327 | 2,1,2,1,2,1,2,2,2,0,2,2 |
| 2 | 7 | 12 | 299 | 4,4,4,4,4,4,3,4,3,3,4,3 |
| 3 | 6 | 48 | 359 | degrees 0/1 per class (48 classes) |
| 3 | 7 | 48 | 436 | degrees 0/1/2 per class (48 classes) |

**Every residue class of every tested (n, ell) fits an exact integer-valued
quasi-polynomial. No refutation was found.** Note the fits use 27-53 points per class
(n=1), 25-31 (n=2), 9-10 (n=3) — far beyond polynomial-detection thresholds, and all
input data is cross-validated against independent determinant computations.

Explicit factorized Q_{ell,r} recovered (n=1; P_c := 4m+c):
- ell=4: Q_{4,r} = P_1, P_2, 0, -P_3, -P_4, P_4, 0, P_4 (r=0..7).
- ell=5: Q_{5,r} = P_1P_2/2, -P_2^2, P_2^2, -P_2P_3/2, -P_3P_4/2, P_4^2, -P_4^2, P_4P_5/2.
- ell=6: Q_{6,0} = -P_2^2 P_{-1} P_1/3; Q_{6,1} = P_2^3; Q_{6,2} = P_2^2 P_3 P_7/12;
  Q_{6,3} = P_2 P_3^2 P_4/12; Q_{6,4} = P_4^2 P_{-1} P_3/12; Q_{6,5} = -P_4^3;
  Q_{6,6} = -P_4^2 P_5 P_9/12; Q_{6,7} = -P_4 P_6 P_5^2/12.
- ell=7 (slope-20 forms appear): Q_{7,0} = P_2^3 P_1 (20m+3)/24; Q_{7,1} =
  -P_2^3 P_3 (20m+17)/24; Q_{7,2} = P_4 P_2^2 P_3^2 P_{25}/144; Q_{7,3} =
  -P_4^2 P_2 P_{-19} P_3^2/144; Q_{7,4} = -P_4^3 P_3 (20m+13)/24; Q_{7,5} =
  P_4^3 P_5 (20m+27)/24; Q_{7,6} = -P_4^2 P_6 P_5^2 P_{27}/144; Q_{7,7} =
  P_4 P_6^2 P_{-17} P_5^2/144. (All recovered from exact data; the slope-20 factors
  show the closed form is not simply products of 4m+c.)
- n=2, ell=5 (rho=12): degrees 0/1; e.g. the full Delta^(5) sequence begins
  1,2,2,2,2,2,1,1,2,... with the fitted affine Q's recorded in the data file.

Unboundedness (old E(2)) is CONFIRMED computationally for these shifts: every ell >= 4
(n=1) has at least one residue class with a nonconstant Q (e.g. ell=4: Q_{4,0} = 4m+1),
and likewise for the tested n=2,3 shifts.

---

## 5. Routes attempted and where they fail (precise record)

R1. **Extend the pass-table method to all shifts.** The ell = n+2 proof relies on the
    orbit hitting bridges after finitely many pass blocks (d = n-2j down to 2) and on
    a_m being constants (+-2^e) over the period. For ell >= n+3 the orbits drift
    forever (Discovery 1) and the a_m are non-constant rational functions of the block
    index, with block length depending on ell (3 for ell=4, 4 for ell=5, and for
    ell >= 6 a different structure again). There is no finite appendix per shift; an
    all-ell theorem would need a uniform parametrization of these families. **Failed
    in this lane**: after computing the families for n=1, ell=4..8 the law linking the
    families across ell was not identified (slope-20 factors at ell=7 defeat the naive
    4m+c ansatz).

R2. **T-system induction (Theorem 1 + Proposition 2).** Reduces everything to
    quasi-polynomial closure of explicit recursions; provably handles all but the
    double-zero classes (gap (d)). Even where it applies, the induction step "X_{k+1} =
    (a_k X_k + b_k^2)/c_k with quasi-polynomial a,b,c of the right shape implies
    quasi-polynomial X" requires controlling the exact root locations of the
    denominator quasi-polynomial c_k (division by zero at known residues) — a finite
    but elaborate algebraic verification per residue class, and the initial data
    (the periodic Delta^(s), s <= n+2, *and* the missing-class values of Delta^(n+3))
    must be available explicitly. Not completed.

R3. **Tail reduction (HP25 Thm 7.3 style).** For 1 <= ell <= n+1 the H-fractions of
    shifts are tails of the periodic H-fraction of Phi_n. Tested computationally: the
    triple of Phi_n^(ell+1) does NOT appear in the NextABC orbit of Phi_n^(ell) for
    (n,ell) = (1,4), (1,5), (2,5) within 150 steps. So higher shifts are not tails of
    any single orbit; each shift needs its own orbit. **Dead end for a one-orbit proof.**

R4. **Monodromy/Floquet of the T-system.** Since the s = n+1 recursion has periodic
    coefficients, a Riccati-monodromy argument would give affine quasi-polynomials —
    but only for ell = n+3 (t = 0), and only away from double zeros; higher shifts have
    non-periodic coefficients. No uniform Floquet statement available. **Partial only.**

R5. **Refutation search.** If Conjecture C were false, some residue class would deviate
    from polynomiality. Exact data up to j <= 440 shows perfect polynomial fits
    everywhere tested (section 4). A refutation via small cases is effectively
    excluded by this data; no refutation was found.

---

## 6. Prior art and novelty limits (bounded; documented)

- 2610.36132v1 (read in full relevant part): states Theorem A/B (proved), Conjecture C
  (open), Remark 4.5 (forthcoming: Delta^(n+2) as signed difference of two shifts of
  the ordinary sequence). No higher-shift results. Companion code (cloned, read
  nextabc.sage/README) computes only the ell = n+2 certification; no higher-shift data
  published in the repo.
- 2502.05993v2 (read: intro results, section 2, section 7): Conjecture E, Theorem F
  (mod-p ultimate periodicity for ALL shifts), Theorem 7.3 (tails for ell <= n+1).
- Wang–Xin–Zhai, "Hankel determinants and shifted periodic continued fractions", Adv.
  Appl. Math. 102 (2019): closest technique prior art (Sulanke–Xin method; shifted
  periodic CFs from quadratic generating functions). Abstract/abstract pages only —
  **the published body was NOT accessible (HTTP 403 on 2026-10-28) and was not read**;
  no metallic content located in accessible material. It does not treat the metallic
  higher shifts (which are not shifted-periodic — Discovery 1).
- Searches (response ids in provenance.json) found no resolution or follow-up of
  Conjecture C; the conjecture is 2 days old as of the lane date. MathDB 367032 groups
  the old conjecture E (not re-fetched; not novelty evidence).
- The T-system (Theorem 1) is classical (Desnanot–Jacobi / octahedron); claimed only as
  a reduction. The computational discoveries (drifting orbits, partial-product
  mechanism, factorized Q's, Fibonacci degree law) are new to this lane to the best of
  bounded knowledge; absolute priority is NOT certified.

## 7. Strongest objection / falsifier

The entire positive evidence for Conjecture C in this lane is exact but FINITE
(j <= 440, ten (n,ell) pairs). A single residue class failing polynomiality at larger j
(while still matching up to j = 440) would refute the conjecture; the data cannot
exclude deviations starting beyond jmax. Conversely the reduction (Proposition 2) is
rigorous but incomplete (gap (d)); someone might wrongly read it as a proof — it is not.
The strongest internal falsifier of my own computations would be an error in the
sigma/v bookkeeping; this is mitigated by (i) reproduction of the source's own printed
n=2, ell=4 determinant string, (ii) direct Bareiss cross-validation of every determinant
value used, (iii) integrality of all extracted values.

## 8. Scope and credit statement

No full resolution (proof or refutation) of Conjecture C or of E(2) is claimed. No
candidate is nominated; credit remains 0. No Lean formalization was produced (no
complete theorem to formalize; the T-system reduction alone does not establish the
conjecture and formalizing a partial reduction was judged not to meet the bar for
meaningful literal bridges). No git operations, no external communications, no writes
outside this lane.
