# W009 review — two-anchor reciprocal fold and two-color test

2026-10-08. Independent T3 review child. Exact algebra and fixed-instance
certificates only. No candidate run, prime/depth sweep, solver, Lean, STATE
or package edit. Verified improvement: **NONE**. No factoring bound changes.

Audited input: research/findings/W009-reciprocal-two-anchor.md
(sha256 1770e04c695cd246…, 5911 bytes). Frozen copies and hashes of it and
of all governing documents are in W009-reciprocal-review-inputs.json.
STATE.md and hypotheses/W009.md hashes match the pinned-review freeze.
Evidence: W009-reciprocal-review-check.py writes ...-check.json
(71 symbolic identities, all passed). Run it from the project root.
Its field-specific checks are fixed instance certificates (symbolic weights
over F_5 and F_7; every subgroup of F_13; two fixed pairs over F_13). They
are not scans. The general arguments are below.
This review does not cover the three-anchor pinned law, which is reviewed by A.

## Verdict

Identities (1)–(5), the subgroup formulas and the trace counts are
**correct as written**, with the scope corrections below. None of them
yields a persistent gain. Three of the brief's interpretive claims need
correction:

1. The "favorable subgroup law" adds nothing at the first step. The actual
   uniform affine start already IS the flat-subgroup case, with G=F_p^* and
   m=p-1. Subgroups with m≤4 have negative drift.
2. The two colors are asymmetric. Infinity is individually absorbing. Zero
   lasts one stage. The zero mass of the final map is exactly the last
   planted pair's mass, so a substantial nonconstant two-color partition
   cannot occur. The case "zero at p, infinity at q" is caught by gcd(V,N)
   alone. Its extra value over gcd(V,N) is only z_p*r_q+z_q*r_p.
3. Each fold is exactly a Newton square-root step, conjugate to squaring on
   the split or nonsplit torus chosen by chi(c). Consecutive frames align
   only when y+w≡0 and c'≡4c. The comparison with trace/torus maps therefore
   has an exact form. A persistent group structure arises only on an event
   of probability about 1/p² per stage, so it is not an available mechanism.

## Item-by-item audit

**(1) Projective update.** It is correct. Res((U-yV)(U-wV), UV) = y*w,
checked by Sylvester determinant. Hence the map has no basepoint and has
degree 2 at a prime iff y*w is nonzero there. The condition y≠w is NOT
needed for validity: y≡w still gives a valid map (z-y)²/z. The y-w test is
needed only for the chart, formula (3) and the gcd channel. If y,w are
units mod N, then gcd(U',V',N)=1 is preserved from [x:1], so every accepted
map is a valid projective map over both primes. Marked images: F(0)=[c:0]=∞,
F(∞)=∞, F(y)=F(w)=0.

Inversion is not needed for the parameters either. With y=U1/V1 and
w=U2/V2, use [(V1U-U1V)(V2U-U2V) : V1V2·UV].

**Fibers.** These are exactly the iota_c-orbits on P^1: {z,c/z} for finite
nonzero z, plus {0,∞}, which maps to ∞. The cross-multiplied identity
(c-yz)(c-wz)=c(z-y)(z-w) is checked. The fixed points are ±√c when c is a
square, so f=2 or 0 in F_p. They are the critical points and are not
merged pairs. Formula (2), F(z)-F(u)=(z-u)(zu-c)/(zu), is checked. The
claim that the partition depends only on c is true. The colors (which
fiber maps to 0) depend on y+w.

**Absorption — correction to obligation wording.** F(∞)=∞ for every (y,w),
so infinity is individually absorbing. Zero is not: 0→∞. The brief's text
"union absorbing, zero moves to infinity" is right. "Neither color is
individually absorbing" is wrong for infinity. As a consequence, for the
map after K stages:

    Z_K = P_(K-1)^(-1){y_K,w_K},   H_K = P_(K-1)^(-1){0,∞},
    z(K) = nu_(K-1)(y_K)+nu_(K-1)(w_K) ≤ 2·max nu_(K-1).

**Chart over Z/N and the conditional sampler.** ell2=s²-v is checked, and
so are sum_c Gamma(c)=ell2 and "the probability of acquiring c is Gamma(c)".
Each local status vector is (U1≡0, V1≡0, U2≡0, V2≡0, y≡w). A proper gcd
appears unless the two primes have identical status vectors. Full failure
has probability sum over the nonclean status vectors σ of P_p(σ)·P_q(σ),
which is not a product event. Clean has probability ell2_p·ell2_q.

Two points the brief omits:

- **The training samples are themselves factor probes.** The chart gcds on
  U_i and V_i are the separate-gcd tests of (5) for the current map P, at
  no extra cost. A failed chart is not wasted work. A full failure is,
  and so is a clean chart whose parameters come from an absorbed-heavy law.
- **ell2=0 at a prime leaves the conditional law undefined.** This happens
  when s=0 (everything absorbed) or nu is a point mass (s²=v); check row
  m=1. Then every attempt at that prime is nonclean. It returns a factor
  if the q-status differs, and fails otherwise. The protocol must state a
  retry cap or stop rule and pay it. E[·|legal] in (4) is meaningless there.
  Retries cost 2 evaluations of O(k) each, an expected 1/(ell2_p ell2_q)
  per stage absent a factor. Once anything is conditioned on, histories
  that survived without a factor are correlated across primes.

**(3) Pointwise law.** It is correct on the legal chart, y≠w both
nonzero: v_new-v=Gamma(c)-(nu(y)+nu(w))², z0_new=nu(y)+nu(w),
h_new=z0+h. This was checked symbolically at every legal pair over F_5 and
F_7, with v_new recomputed from the orbits. The planted 2·nu(y)nu(w) lies
inside Gamma and is not double counted. The full collision gain is
2·z0·h+Gamma, as claimed.

**(4) Averaged law.** Both numerators are verified exactly: the drift
sum_c Gamma²-2·s·u3-2·v²+4·q4 and the absorption 2(s·v-u3). The term
sum Gamma² is ordinary multiplicative energy minus the diagonal-square
contributions D(c)=sum_{a²=c} nu(a)², i.e. sum(Gamma+D)² minus the cross
and D² terms. The brief's wording "diagonal removed" is accurate.

**Subgroup drift.** Both formulas are correct. They were simplified
symbolically and certified on every subgroup of F_13:

| m | drift (s=1) | drift / v |
|---|---|---|
| 2 | -1/2 | -1 |
| 3 | -2/9 | -2/3 |
| 4 | -1/24 | -1/6 |
| 6 | 1/30 | 1/5 |
| 12 | 13/264 | 13/22 |

Statements about fixed points are correct as stated in G: odd m gives one
root in G, since -1∉G; even m gives 2 or 0. iota_c preserves G. Corrections:

- Drift is positive only for m≥5. "Nearly doubles" means relative drift
  1-5/m (odd) or ≈1-5/m (even), never more than doubling. It improves with
  LARGER m.
- **The uniform affine start is this case, with m=p-1 even and
  s=(p-1)/p.** A favorable subgroup law therefore offers nothing at step 1
  beyond the free start. A smaller G only raises v=s²/m, and obtaining it
  through x^d is the gcd(d,p-1) order problem, as the brief notes. The
  claim must be restated as "the free start already gives the one-step
  near-doubling." It is not a separate favorable law.

**Trace count.** n(b)=1+chi((b+y+w)²-4c) is correct: the roots of
z²-(b+y+w)z+c are automatically nonzero. Also n(∞)=1 and n(0)=2, because
the discriminant is (y-w)², a nonzero square. Normalization:
sum_b n(b)=p+sum_x chi(x²-4c)=p-1, plus 1 for ∞, totals p. An additional
exact result follows. With z_c=#{x:x²=4c}∈{0,2}, i.e. 1+chi(c):

    v_new = (2p-6-z_c)/p²,  Δv = (p-5-z_c)/p²   (uniform start, fixed c).

This was checked for c=4 (square) and c=2 (nonsquare) mod 13, giving
6/169 and 8/169. The Gamma-weighted average over c recovers the even-m
subgroup formula with m=p-1, which cross-checks (3), (4) and the counts.
Step 1 is therefore fully explicit. The open problem is the energy of this
trace law at step ≥2, which the parent owns. I did not derive it.

**(5) Two-color probability.** It is correct for a fixed valid map with a
uniform CRT input, where local inputs are independent. U and V never vanish
together locally, and both separate gcds are needed. Exact decompositions,
checked symbolically:

    s_factor - s_V  = z_p·r_q + z_q·r_p,
    s_factor - s_UV = z_p·h_q + h_p·z_q.

So "zero at p, infinity at q" is already found by gcd(V,N) alone, since V
vanishes mod q only. The U test adds only zero-versus-neither events.
Every added channel is bounded by z_p+z_q ≤ 2(max nu_p+max nu_q)
of the previous laws. Masking certificate: a stage-K pair (zero@p, ∞@q)
becomes (∞,∞) at K+1, and only full gcds remain. Two-color events are
therefore available only at the stage of their creation. Retesting earlier
maps is not free, since each probe costs O(k). "Both local maps reach a
nonconstant two-color partition" is structurally impossible beyond a
zero mass of one planted pair per stage. The benefit is an O(max nu)
extra channel, not a new partition.

## Exact conjugacy and scoped prior art (comparison requested)

With r²=c (r∈F_p, or r∈F_{p²} if chi(c)=-1), set x=(z-r)/(z+r). Then

    (z+c/z-2r)/(z+c/z+2r) = x²,   and iota_c becomes x -> -x.

Both identities are checked. So F = 2·Newton_c - (y+w), where Newton_c is
z->(z+c/z)/2, the Newton/Heron square-root map. Each fold is
Möbius∘squaring∘Möbius on the split torus F_p^* if chi_p(c)=1, or the
norm-one torus of order p+1 if chi_p(c)=-1. The choice is made separately
at p and at q. The output frame is {-s0±2r} with s0=y+w. The next input
frame is {±r'}. These sets are equal iff s0=0 and r'²=4c (sum and product
check). Only then does the composite reduce to x->x^(2^k) in one torus.
That is the Lucas/p±1-type powering, which needs group-order luck to
factor. For sampled y,w this alignment occurs with probability about 1/p²
per stage, so it is not a usable route. Generic interstitial Möbius maps
destroy subgroup or coset structure. This is the exact reason the subgroup
law does not persist, and it agrees with the brief's caution.

Prior art, scoped:

- The Newton/squaring conjugacy for quadratics is classical (Cayley–Schröder).
- Ugolini studied the functional graphs of the FIXED maps x+x^{-1} in
  characteristic 2, 3 and 5, and k(x+x^{-1}) in odd characteristic. The
  characteristic-2 paper links the map to duplication on a Koblitz curve:
  [arXiv:1107.4565](https://arxiv.org/abs/1107.4565),
  [1108.1763](https://arxiv.org/abs/1108.1763),
  [1110.0968](https://arxiv.org/abs/1110.0968).
- I only read abstracts and introductions. None of these covers a changing
  sampled c and translation, or a factor-acquisition rate. They are
  comparators for fixed-map cycle structure, not bounds for W009.

## Decisive counterexamples to stated or implied universal claims

- "Neither color is individually absorbing": false for ∞, since F(∞)=∞
  for every legal (y,w).
- "A flat subgroup law is favorable / nearly doubles v": false for m≤4
  (F_13 rows: m=2,3,4 give negative drift). For large m it holds already at
  the free uniform start, m=p-1.
- "A nonconstant two-color partition can be reached": the final zero mass
  is identically nu(y_K)+nu(w_K). No stage carries more zero mass than one
  planted pair.
- "Zero@p/∞@q needs the U/V split": gcd(V,N) alone detects it.
  The split matters only relative to gcd(U·V,N).

## Actionable corrections for the parent

1. Replace "favorable input law" with: "step-1 near-doubling is free
   (uniform start = F_p^*, Δv=(p-5-z_c)/p² exactly); subgroups m≤4
   contract."
2. Restate the two-color benefit as the extra channel z_p·r_q+z_q·r_p over
   gcd(V,N), bounded by the planted-pair masses. Delete the "nonconstant
   two-color partition" framing.
3. Add an ell2=0 stop/cap rule. Count the training gcds as probes, and
   count full chart failures as paid losses.
4. Record the Newton/torus conjugacy and the frame-alignment condition
   (s0=0, c'=4c) as the exact boundary with p±1/Lucas methods. Any
   persistence argument must work through generic interstitial Möbius
   maps, not torus subgroups.

Persistence of non-forced energy at step ≥2 remains unproved. Neither (4)
nor the subgroup computation supplies it. No depth sweep is warranted by
these identities.
