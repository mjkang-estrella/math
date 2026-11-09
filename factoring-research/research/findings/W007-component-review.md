# W007 component factorization — independent review

2026-10-08. Claude Opus 5.5 T3 review of the parent's
[component factorization note](W007-component-factorization.md). Symbolic work
only. No candidate runs, prime-field enumeration, shared-state edits, solver or
Lean changes. The W008 displacement audit is not duplicated here.
Verified factoring improvement: **NONE**.

## Disposition

The parent's statements hold, with three corrections in scope. One addition
extends the range.

1. **Accepted:** the all-depth identity (1), the count L_k=1+k(k+1)/2, the degree
   sum, the linear-factor count for k>=1, absolute irreducibility, distinctness,
   the exact finite-field mean T_f/p^2, the Weil–Parseval bound (3), the union
   bound (4) with its closed form for B_k, and the intersection lower bound (5).
2. **Corrections:**
   - The hypothesis 2^(k-2)<p in (4) is not needed.
   - The irreducibility argument has a step the note leaves out: the total degree
     of each component equals its X-degree. Any degree-based point count needs
     that fact, and homogeneity gives it.
   - The linear factors are distinct in every characteristic. Odd characteristic
     is needed only for irreducibility.
3. **Strengthened:** (5) needs no Bézout theorem and no field-size condition.
   An elementary elimination lemma gives a sharper pair constant.
4. **New:** a Weil–Parseval bound weighted by collision count replaces (D-1)^2
   by (D-1)*(expected fiber size - 1). Feeding the accepted law E[Δz]=v back into
   that bound proves

       |E[m_k] - L_k| <= A_k/sqrt(p) + Pi_k/p    whenever  k*2^k <= sqrt(p)/4,

   with explicit A_k <= k*2^k. The range with o(1) error therefore extends from
   k<=(1/4-ε)log2 p to k*2^k=o(sqrt p), which is degree up to about sqrt(p)/log p.
5. **Consequence (regime-qualified, implementation-specific):** a coupling
   argument removes survival conditioning from success upper bounds. Inside that
   regime, this acquisition rule needs Ω(p/log^2 p) fresh evaluation points for
   constant success, a power worse than the rho control. Every possible gain lies
   at degree 2^k ≳ sqrt(p)/k, where no estimate is known. Section 9 names the
   missing estimate exactly.

This is not a factoring lower bound. It covers neither other acquisition rules
nor depths beyond the regime.

## 1. The identity and its conventions

Over any commutative ring, P_(i+1)(X)-P_(i+1)(Y)=(P_i(X)-P_i(Y))(P_i(X)+P_i(Y)-a_i)
follows from expanding y(y-a). Iterating with Y=r_j and a_i=P_i(r_i) gives
P_j(X)-a_j=(X-r_j)∏_(i<j)Q_(i,j)(X), and then (1). Accepted.

- The count is L_k=1+k+k(k-1)/2. The degree sum is
  1+k+Σ_(j<k)(2^j-1)=2^k.
- k=0: P_0=X, L_0=1, with one linear factor. The phrase "exactly 2k linear" is
  correctly restricted to k>=1.
- k=1: P_1=X(X-r_0), so E[m_1]=2-1/p exactly. Section 6 reproduces this value
  as an equality case.
- Q_(i,j) depends only on r_0,…,r_i,r_j, because P_i's coefficients are
  polynomials in r_0..r_(i-1). The identity holds for every value of the r's,
  however they were chosen. Only the probabilistic statements need freshness.
- Distinct linear factors: X-r_j=X+r_m-r_0 would force r_j+r_m=r_0 as
  polynomials. That is impossible in any characteristic (for j=0 it reads r_m=0).
- Certificate: `certify.py` expands (1) exactly over Z for k<=4 (item 2).

## 2. Irreducibility, distinctness, and the degree that point counts need

**Parent's argument (accepted).** Let K=F_p(r_0..r_(i-1)) and D=2^i>=2. Then
G=P_i(X)+P_i(Y)-P_i(Z) has top form X^D+Y^D-Z^D in (X,Y,Z). Since p∤D, that
form is a smooth plane curve, hence irreducible over the closure of K.

- A nontrivial factorization of G would induce a nontrivial factorization of
  its top form, because every nonconstant factor has a nonzero top form of the
  same degree. So G is absolutely irreducible over K.
- G is monic in X, hence primitive over F̄_p[r_<i]. Gauss's lemma then gives
  irreducibility in F̄_p[X,r_0..r_(k-1)]. Extra variables that G does not
  involve cannot split it.
- Distinctness of the factors: X-degree separates different i. For equal i,
  dependence on r_j separates different j, and two monic polynomials that are
  associates are equal.

**Independent second proof, and the missing degree fact.**

- *Homogeneity.* By induction, P_m is homogeneous of total degree 2^m in
  (X,r_0..r_(m-1)): P_m(r_m) is homogeneous of the same degree. Setting
  r_0=…=r_(m-1)=0 gives X^(2^m). So Q_(i,j) is homogeneous of degree 2^i, and
  restricting to r_0=…=r_(i-1)=0 gives the Fermat form X^D+r_j^D-r_i^D.
- *Irreducibility from the restriction.* A factorization of a homogeneous
  polynomial is a factorization into homogeneous factors. The restriction of
  each factor stays nonzero and keeps its degree. So irreducibility of the
  restriction gives irreducibility of Q_(i,j) over F̄_p.
- *Irreducibility of the Fermat form, elementarily.* In F̄_p[Y,Z],
  Y^D-Z^D=∏_l(Y-ζ^l Z) has distinct linear factors because p∤D. Eisenstein at
  the prime Y-Z, applied to X^D+(Y^D-Z^D) as a monic polynomial in X, gives
  irreducibility.

The same homogeneity gives what the note's degree arguments assume without
saying so: **the total degree of Q_(i,j) in all k+1 variables is 2^i**, equal to
its X-degree. Without this, the coefficients a_l (polynomials of degree 2^l in
the r's) could have pushed the hypersurface degree far above 2^i. Any
Lang–Weil, Cafure–Matera or Bézout constant would then change. Certified for
k<=5 (items 1 and 3).

**Conclusion.** For every odd p and every k>=0, V(P_k)⊂A^(k+1) over F̄_p has
exactly L_k irreducible components. Each is a hypersurface of degree 1 or 2^i,
defined over F_p. In characteristic 2 the top form is (X+Y+Z)^D and the
argument fails. That case is out of scope.

## 3. The exact finite-field mean and the freshness it needs

Fix r_<i and write f=P_i. Then ρ_(i,j)=#{x:Q_(i,j)(x)=0} satisfies

    E_(r_i,r_j)[ρ_(i,j)] = p^(-2) #{(x,y,z): f(x)+f(y)=f(z)} = T_f/p^2

exactly, provided (r_i,r_j) is uniform on F_p^2 given r_<i.

- In the unstopped process every r_j is fresh and uniform, so this holds.
- The note's phrase "intervening coefficients generated adaptively" adds
  nothing in this process: the a_l are deterministic functions of the r's. The
  correct general condition is freshness of r_i given r_<i and of r_j given
  everything before it.
- Reusing an r, or correlating r_j with r_i, invalidates (3) for that pair,
  while (1) still holds.
- Uniform residues modulo N reduce to uniform residues modulo p, so this is the
  CRT tape of the actual computation.

## 4. Weil–Parseval (3) and the union bound (4)

**Kowalski, Theorem 3.2, printed p31** (snapshot hashed). Hypotheses: f∈F_q[X]
of degree d, a non-trivial additive character ψ, d<q and (d,q)=1. Conclusion:
|Σψ(f(x))|<=(d-1)√q. For q=p odd and D=2^i<p these hypotheses hold. The
printed remark directly after the theorem (p32) says d<q is redundant, since the
bound is trivial for d>=q. Indeed (D-1)√p>=p√p whenever D>p.

Derivation of (3), checked:

- T_f=p^2+p^(-1)Σ_(t≠0)S(t)|S(t)|^2, using S(-t)=conj S(t).
- Σ_(t≠0)|S(t)|^2=pC_f-p^2 by Parseval.
- C_f<=pD, since f(T)-c is monic of degree D.
- Hence |T_f-p^2| <= max|S|·(C_f-p) <= (D-1)^2 p^(3/2).

The union bound gives (4). The certificate verifies the closed form of B_k and
B_0=B_1=B_2=0 (item 5).

**Correction:** (3) and (4) hold for every odd p and every k. The proviso
2^(k-2)<p can be dropped, though (4) becomes weaker than the degree cap 2^k
once 2^k>9√p.

**Alternative route.** Cafure–Matera Theorem 5.2 has no field-size hypothesis
for absolutely irreducible hypersurfaces. With δ=2^i, using Section 2, it gives
|E[ρ_(i,j)]-1|<=(δ-1)(δ-2)/√p+5δ^(13/3)/p. That is slightly better at leading
order and worse in the second term. Section 5 makes both obsolete.

## 5. New: a collision-weighted bound, and depth up to degree ≈√p

The proof of (3) actually gives, for every fixed f of degree D,

    |T_f/p^2 - 1| <= (D-1) γ(f)/√p,    γ(f) := C_f/p - 1 = E_x[#f^(-1)(f(x))] - 1.   (3')

(3) is the worst case γ<=D-1. For the tower, γ is small and computable from
the accepted drift.

- Split C_f by the zero fiber: C_(P_i)=m_i^2+Σ_(y≠0)n(y)^2. Also
  E_(r_i)[m_(i+1)-m_i]=p^(-1)Σ_(y≠0)n(y)^2; this is the accepted E[Δz]=v.
- So E[γ_i]=E[m_i^2]/p+E[m_(i+1)-m_i]-1.
- Applying the union bound to P_i-a_i=(X-r_i)∏_(l<i)Q_(l,i) gives
  m_(i+1)-m_i<=1+Σ_(l<i)ρ_(l,i). Also m_i<=2^i.

Let ε_i bound |E ρ_(i,j)-1|, with ε_0=0. This yields a closed recursion:

    ε_i = (2^i-1)/√p · ( i + Σ_(l=1)^(i-1) ε_l + 2^i U_i/p ),
    U_i = L_i + Σ_(l=1)^(i-2) (i-1-l) ε_l,
    L_k - Σ_(i=1)^(k-2)(k-1-i)ε_i - Pi_k/p  <=  E[m_k]  <=  U_k.

This recursion holds for all k and all odd p.

**Theorem (regime).** Let p be an odd prime and k>=0 with k·2^k<=√p/4. Then
ε_i<=(i+1)(2^i-1)/√p for 1<=i<=k-2, and

    L_k - A_k/√p - Pi_k/p  <=  E[m_k]  <=  L_k + A_k/√p,
    A_k = Σ_(i=1)^(k-2)(k-1-i)(i+1)(2^i-1) = (k-3)2^k + k + 3 - (k^3-k)/6 <= k 2^k,
    Pi_k = (4^(k+1)-3k-4)/9.

In particular |E[m_k]-L_k| < 1/4 + 1/(9k^2) throughout the regime.

*Proof.* Strong induction on i.

- Σ_(l=1)^(i-1)(l+1)2^l=(i-1)2^i (item 6). Since (i-1)2^i<=k2^k/4, this gives
  Σ_(l<i)ε_l<=1/16.
- U_i<=L_i+(i-2)/16<=(i+1)^2.
- 2^i U_i/p <= 4i·(i2^i)/p <= 1/128, using i<=i2^i/2<=√p/32.
- So the bracket is at most i+1, which gives the bound on ε_i.
- The closed form of A_k follows from Σ s2^(-s) and Σ s^2 2^(-s). It is
  certified for k<=60. ∎

**Consistency with exact data.**

- k=3: 7-(1+4/p)/√p-27/p <= E[m_3] <= 7+(1+4/p)/√p. This contains the earlier
  exact value 7-23/p+O(p^(-2)).
- The single nonlinear component at i=1 is elementary. Substituting
  (v-w)(v+w) shows u^2+v^2-w^2=c has p^2+pχ(c) solutions for c≠0 and p^2 for
  c=0. Hence E[ρ_(1,j)|r_0≠0]=1+1/p. The true error is O(1/p), so (3') is far
  from sharp at small degree.
- The earlier depth-4 values at p=17 and p=31 (7.88 and 9.11) lie outside the
  regime and are consistent with (4).

**Without Weil, only the trivial bound.** Cauchy–Schwarz gives
E[ρ_(i,j)|r_<i]<=1+γ(P_i). That yields only E[m_(k+1)]<=2E[m_k]+O(E[m^2]/p),
which is the degree cap. All the information below the degree cap comes from
cancellation in the non-trivial character sums.

## 6. The intersection estimate (5)

**Accepted, via the source route.** Each pair of distinct factors F,G meets in
a set of dimension k-1. By (7), its degree is at most δ_Fδ_G, using the
homogeneous degrees from Section 2. By Lemma 2.1 it then has at most
δ_Fδ_G p^(k-1) points. Neither result has a field-size condition. Bonferroni
plus the two-sided (3) gives (5).

**Elementary replacement (certified for every pair at k=5, item 4).**

- For every pair of distinct factors there is a training variable u≠X such
  that G does not involve u and ±F is monic in u of degree δ_F.
- Case table: use r_j for the factor with the newer j. For equal j, use r_i
  of the larger i. For X-r_j against X+r_j-r_0, use r_0.
- Every factor is monic in X with X-degree δ.
- So #{F=G=0}<=δ_F·#{G=0}<=δ_Fδ_G p^(k-1), with no geometry and no
  characteristic hypothesis.
- Bonferroni needs no irreducibility either. Irreducibility is only the
  geometric reading of L_k.

The exact pair sum is Pi_k=Σ_(c<c')δ_cδ_(c')=(4^(k+1)-3k-4)/9<=2^(2k-1).
At k=1, Pi_1=1, and the lower bound 2-1/p equals E[m_1] exactly. So (5) is valid
for all odd p and all k, with 2^(2k-1) replaceable by Pi_k.

## 7. Conditioning on r_0≠0

The upper bounds (4) and Section 5 hold verbatim conditional on r_0≠0.

- For i>=1, (3') holds for each fixed r_<i, and {r_0≠0} lies in σ(r_<i).
- The i=0 factors are linear, with exactly one root each.
- The recursion terms E[m_i^2], E[m_(i+1)-m_i] are conditional expectations
  given r_<i, so they are unchanged by this conditioning.

The lower bound holds with Pi_k/(p-1) in place of Pi_k/p. The fixed-k limit L_k
and the regime theorem are unchanged.

## 8. Stopping, survival, CRT, and what the regime implies

- **CRT.** Accept the parent's repair. With exactly uniform residues modulo N
  and componentwise ring updates, the fixed-horizon unstopped p- and q-histories
  are independent. Conditioning on a global stopping event couples them.
- **Survival is not needed for success upper bounds.** Couple the stopped run
  with the unstopped run on the same tapes. The stopped run can output a proper
  factor only if some tested value is ≡0 modulo a prime ℓ|N. Allowed tests
  include x-r_j, P_l(y)-a_l, any Q_(i,l)(y), and P_l(y) before or after
  multiplication. Every such value is a factor of P_j(y), at the level j where
  point y is used, so the event lies inside {ℓ|P_j(y)}.
- **The resulting bound.** Abandoning on gcd N only shortens a run. For a run
  with depth k and T probes fixed in advance (fresh training r_j used on P_j,
  fresh probes on P_k):

      Pr[run outputs a proper factor] <= Σ_(ℓ∈{p,q}) ( Σ_(j<k) E[m_j(ℓ)] + T·E[m_k(ℓ)] ) / ℓ,

  using unstopped marginals only.
- **Survival corrections are small anyway.** For a survival event S of
  probability >=1-η, |E[m_k|S]-E[m_k]|<=2^k η/(1-η). Inside the regime,
  the p-history depends only on S_p, η<=k(L_k+1)/p, and the correction is
  at most L_k/(4√p)·(1+o(1))=O(k^2/√p).
- **Regime consequence.** Let p<q and k_s·2^(k_s)<=√p/4 for every run in a
  schedule fixed in advance, restarting on gcd N. Since m_j<=m_k pointwise, the
  bound gives Pr[success] <= 2M(L_(k*)+1/4)/p, where M=Σ_s(k_s+T_s) counts
  evaluation points. Success at least 1/2 therefore needs
  M>=p/(4L_(k*)+1)=Ω(p/log^2 p) evaluation points, each costing at least one
  arithmetic operation. The rho or W006 batch-detector control is Õ(√p).
- **What this does not cover.** Schedules whose probe counts adapt to the
  observed residues modulo N within a run are not covered. Such values can
  correlate with m_k, and E[m_k·1{probe}] does not factor. Depths beyond the
  regime are not covered.

## 9. What remains open, exactly

**The regime boundary is where every gain lies.** Inside the regime the rule
loses. Matching rho needs E[m_k] of order √p. Beating it needs E[m_k]≫√p, which
needs 2^k≫√p, outside the regime. There, (3') no longer controls the components
with 2^i≳√p/i.

**Missing estimate.** For 2^i≳√p/i, a bound on the parameter average

    E_(r_<i)[ p^(-3) Σ_(t≠0) S_(P_i)(t)|S_(P_i)(t)|^2 ] = E[ p·Σ_(u,w) μ_i(u)μ_i(w)μ_i(u+w) ] - 1,

the additive triple excess of the value law μ_i of the composed tower.

- If this excess is o(1/k^2) at all depths, then E[m_k]=L_k+o(1) up to
  k≈log2 p. The rule is then hopeless at every depth: success per point is
  O(log^2 p/p).
- If the excess is large, the images of the tower have additive structure, and
  that structure is the only possible source of gain.
- **Exact transfer identity.** With a=a_(i-1),

      S_(P_i)(t) = p^(-1) Σ_s S_(P_(i-1))(s) K_a(t,s),
      K_a(t,s) = Σ_y e_p(t y^2 - (ta+s) y),

  and |K_a|=√p for t≠0. The obvious ℓ^1 bound from this identity is the
  trivial √(pC)>=p. Any useful estimate must exploit the phases in s and the
  law of a_(i-1).
- No primary source on beyond-Weil sums for composed quadratic towers was
  checked. That bounded literature question should come before any derivation.

**Acquisition computation the result leaves unresolved.** Q_(i,j)=P_i-b_(ij)
with b_(ij)=a_i-P_i(r_j). So the roots of each component form the P_i-fiber
over b_(ij). Under fresh r that fiber has expected size 1+o(1) whatever its
degree. A large fiber needs the nested backward discriminants a_l^2+4w of the
quadratic tower to be squares modulo the unknown p. A full fiber needs 2^i-1
such conditions.

- The observable Jacobi symbol modulo N gives only χ_pχ_q.
- Forcing squares globally modulo N plants roots that are known residues
  modulo N. Those give gcd N, or, through intermediate tests, a known-point
  collision priced exactly like the batch-collision control.

So the missing operation is a paid procedure that biases local squareness of
the tower discriminants at an unknown prime without global square roots.
Equivalently, it must create additive structure in the images of P_i. None is
supplied by the parent, the earlier audits, or this review.

## 10. Evidence and scope

- [`W007-component-review-certificates/certify.py`](W007-component-review-certificates/certify.py)
  is stdlib-only exact polynomial arithmetic over Z. Output is in
  `certificates.txt`: six PASS lines, run with `python3 -I`, 2.3 s.
- It checks finite instances of statements proved above for all k. It is
  not evidence for anything beyond those proofs.
- [`W007-component-review-sources/`](W007-component-review-sources/SOURCES.md)
  holds the Kowalski and Cafure–Matera PDFs with text extractions and read
  scopes, plus a snapshot of the parent note.
- The delivery hashes are in `W007-component-review-delivery.sha256`.
- Earlier fixed-cover, PTE, tau, residual and W008 audits are untouched.
- No STATE, registry, solver, Lean, package, commit or publication change.

**Next decisive question:** for degrees 2^i between √p/i and p, does the
parameter-averaged additive triple excess of the composed quadratic tower stay
o(1/i^2)? Settle the primary literature on character sums of iterated or
composed polynomials first. Pursue a correlated acquisition only if it supplies
the local-squareness bias of Section 9 at a paid cost.
