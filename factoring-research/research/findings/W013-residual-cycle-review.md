# W013 Card A residual-cycle review

2026-10-08. Independent review sub-agent; the parent is still principal ideator.
**Verdict: Card A's identities are correct, with one sign correction to its
proposed update rule. The divided-norm state, update and edge labels are exactly
the Gower--Wagstaff/continued-fraction principal-cycle machinery. A coefficient
collision is a two-term CFRAC-type square relation. Whether it yields a factor is
decided by genus/ambiguous-class structure, and this review proves the cases
where it cannot. No end-to-end bound is earned. Verified improvement: NONE.**
Card B is out of scope and was not audited.

## Freeze, scope and evidence

The verbatim brief (`-brief.txt`) and the nine load-bearing inputs (project
instructions, W013, W012 square-coordinate, geometry-disposition, navigation-trap)
were copied before analysis. Their hashes are in `-inputs-manifest.json`. The
primary source was fetched once from https://homes.cerias.purdue.edu/~ssw/squfof.pdf
(SHA-256 `51f8133c…bde516`) and kept under `-source/` with a text extraction. I
read §§1–4.6 and §§5.4–7: the background, the algorithm, the queue/properness test
and the complexity assumptions. Section 5's multiplier theorems were only skimmed.

One fixed exact certificate was preregistered (`-certificate-brief.md`, frozen
before the code) and run once. All 16 checks passed and none failed. One extra
structural check was added afterwards. It is labelled POST-HOC and also passed.
There was no timing, no sweep and no search over N. The only composite used is
G–W's own example N=22117019=4451·4969, plus six tiny moduli for root counts.
The W012 D selector audit was not duplicated. There was no delegation, no package
install, no commit, and no edits to the solver, Lean, STATE or registry.

## 1. Raw square-coordinate recurrence: correct, structurally weak

With t=isqrt((N-1)//a)+1 (the exact ceiling, as in W012 D) and b=a·t²-N,
we get b≡a·t² (mod N). Along a path, a_i≡a_0·R_i² with R_i=∏t, so a return
a_i=a_j with a_0 a unit gives (R_i/R_j)²≡1. The envelope 0≤b<2√(Na)+a holds
exactly (certificate C4, as an integer inequality). The exponent map β↦(1+β)/2
is correct. On the fixed N, the 25-bit states reach 26 bits by step 4.

Additional qualifications:
- If a≥N then b=a-N, and if a<N then b<3N. The walk is therefore a deterministic
  map on fewer than 3N states, and its first repeat is a whole-integer collision.
- t depends on the integer representative, not on a mod p. A collision modulo an
  unknown prime p of N therefore does not propagate. The Floyd/gcd trick behind
  Pollard rho is unavailable, and a random-map heuristic would put the repeat near
  √N states, which is worse than rho.
- Each step corresponds to a value of the form (a,0,-N), whose discriminant 4aN
  changes from step to step. There is no shared class-group structure.

## 2. Divided-norm identity and update: correct; the rule needs a sign fix

The identity (P+kb)²-N = b·(a+2kP+k²b) + (P²-N-ab) holds as a polynomial
identity (C1, checked on a full 4⁵ product grid; degree ≤2 in each variable).
With P²=N+ab, the next coefficient c is exact. The label P/a satisfies
(P/a)²≡b/a, provided a is a unit.

**Known-method mapping.** The state (a,P,b) with P²-ab=N is exactly the binary
quadratic form (a,2P,b) of discriminant 4N. G–W §2.4 writes the principal cycle
as F_n=((-1)^{n-1}Q_{n-1}, 2P_n, (-1)^n Q_n) with N=P_n²+Q_{n-1}Q_n, i.e.
a=(-1)^{n-1}Q_{n-1} and b=(-1)^nQ_n. Certificate C2 reproduces rows 1–18 of
G–W Table 1.

**Sign correction.** A reduced form needs √N-|b|<P<√N (G–W §2.1.2). That open
window of length |b| contains exactly one integer ≡P (mod |b|), namely P itself.
Card A's literal rule, "P'=P+kb near √N", therefore picks k=0 on every reduced
state, which gives c=a: the trivial reverse edge. C2 confirms this on all 17
checked edges. The forward step is G–W's ρ, P_{n+1}=q_nQ_n-P_n≡-P (mod b).
In Card A's parametrization, that is P'=P+kb≈-√N, optionally followed by
P'↦-P' (c depends only on P'²). Negating P only flips the sign of a label.
C2 confirms the corrected rule reproduces ρ on every row.

**Reverse edges, exact.** P'=P gives label product P²/(ab)≡1, and P'=-P gives -1
(C2, both exact). These are trivial for any gcd.

**There is no branching among reduced states.** Every reduced form has a unique
reduced right neighbour and a unique reduced left neighbour (G–W §2.1.2). The only
reduced successors of (a,2P,b) are the backtrack and ρ, so a non-backtracking
reduced walk *is* the deterministic principal cycle. "Mixing of non-backtracking
walks" is vacuous here. Any other k gives a non-reduced form with |c|≈k²|b|.
That form is still equivalent to the start or its inverse (the class alternates
C, C⁻¹), so reduction returns to the same cycle or cycles. Such moves are jumps
along the cycle, as in Shanks' infrastructure (G–W §2.4), not new states.

**Cost per step.** Each step costs O(log N)-bit form arithmetic plus one modular
inverse for the label, or projective numerator/denominator tracking instead.
gcd(a,N)>1 on a reduced state already gives a proper factor, because |a|<2√N<N.

## 3. Labels are CF convergent numerators mod N (CFRAC relations)

The edge label is the image of μ=(P+√N)/a, which has norm b/a, under the map
Z[√N]→Z[√N]/(√N)≅Z/N. Along the principal cycle, C2 checks exactly that
(A_n+B_n√N)·Q_{n-1} = (A_{n-1}+B_{n-1}√N)(P_n+√N) and A_n²-NB_n²=(-1)^nQ_n.
These are G–W §2.2's facts. C2 also checks that the product of Card labels is
≡±A_n (mod N) for n=1..18. Card A's "labelled residual" is therefore the CFRAC
relation A_n²≡(-1)^nQ_n (mod N) with Q_n left unfactored.

## 4. Coefficient collisions: what they can and cannot output

A collision a_i=a_j (same sign) inside one cycle gives u=Λ_{j-1}/Λ_{i-1} with u²≡1.
Here Λ is the label prefix product, and Λ_{n-1}²≡a_n is checked in C3. This is a
two-relation CFRAC dependency: (-1)^iQ_i·(-1)^jQ_j=a² is a square without any
factoring, like a large-prime-variation pairing whose "large" cofactor may be any
integer. If the two coefficients have opposite signs, u²≡-1 and no factor follows
directly.

**Lemma (ramified-sign).** Let p∥N with p odd, and let 𝔭=(p,√N), so 𝔭²=(p). Let
λ∈Q(√N) have norm 1 and be a unit at 𝔭. Write λ=β/σ(β) (Hilbert 90). Then
λ≡(-1)^{v_𝔭(β)} (mod 𝔭).
*Proof.* v_𝔭(√N)=1 and σ(√N)=-√N. Put β=(√N)^vγ with γ a 𝔭-unit; then
λ=(-1)^v·γ/σ(γ). σ acts trivially on the residue field F_p, so γ/σ(γ)≡1. ∎

Consequently u yields a proper divisor exactly when these parities differ across
the primes of N. When u≢±1, gcd(u-1,N) is always proper, because N|(u-1)(u+1).

**Classification** by ideal of norm |a|. Via the form–ideal dictionary of G–W §2.4,
the class of P mod |a| fixes the ideal. Proofs here rely on the standard
dictionary and were checked on the certificate N, not formalized.
- *Same ideal* (P_j≡P_i): impossible inside one period, because a reduced form is
  determined by (a, P mod |a|). C3 found 0. A full return of the state gives the
  label of the period unit ε.
- *Conjugate* (P_j≡-P_i): then Γ_j=η·σ(Γ_i) for a unit η, so u≡±image(η), a power
  of the unit image. All conjugate collisions together carry at most one bit, the
  one already given by the classical half-period ambiguous form. This covers every
  collision where |a| is a prime power, since such a norm has only two primitive
  ideals. C3: all 400 conjugate collisions lie in ±⟨image ε⟩. Here image ε≡1, so
  all 400 are trivial (0 proper).
- *Mixed* (all other cases): this needs |a| to have at least two distinct primes
  not dividing 4N. The differing part 𝔡 lies in a 2-torsion class, so whether u is
  proper is the ambiguous-class question that SQUFOF faces at its square-root step
  (G–W Assumption 4.19, a heuristic). POST-HOC: all 92 mixed collisions have ≥2
  such primes; 56 of them gave a proper split. These single-N counts describe one
  cycle; they are not probability evidence.

**Prior-art answer.** The state, the update (after the sign fix), the reverse-edge
behaviour, the labels and the trivial-root classification are known machinery.
- The state, update and labels are G–W/CF continued-fraction machinery.
- SQUFOF's queue stores (Q, P mod Q) for small coefficients. The test in
  Proposition 3.2 compares a square root's coefficient and residue with earlier
  coefficients on the cycle, using exactly this comparison, to recognize trivial
  ambiguous roots ±1, ±2.
- Combining relations with equal Q is CFRAC dependency combination.

What G–W do *not* do is treat a mixed collision itself as the factoring event: they
use square forms and the reverse infrastructure walk. I read no primary source
stating the "pure Q-collision on one period" variant, but it is a degenerate case
of CFRAC relation combination (Morrison–Brillhart is an unaudited pointer).
**No novelty is supported.**

## 5. Output, sign and stopping scope; no end-to-end bound

**Stopping rule.** Use the CF/ρ walk, keep a store of signed coefficients
(including P mod |a|), and test gcd(u±1,N) at every same-sign collision. Stop at
a proper split, at gcd(a,N)>1, or when Q_n=1 returns (end of the period).
Reaching the period's end fails for this multiplier. Restarting with kN is paid
and is G–W §5 territory.

**Assumptions.** The lemma needs odd p∥N. The analysis assumes squarefree N and a
fundamental discriminant, as G–W's analysis does. Even N, prime powers and perfect
squares need separate handling. An odd prime power has r=2, so no collision can
ever be nontrivial (C5).

**Cost is a heuristic, not a bound.** Reduced coefficients range over about √N
values. Birthday on that range suggests about N^{1/4} steps and N^{1/4} stored
coefficients, *if* the coefficients behave randomly and mixed collisions occur at
a constant rate. Neither is proved. Even granting both, this is the same order as
SQUFOF's heuristic A[W]≈1.77·N^{1/4} (Theorem 4.22, for N≡3 mod 4 with two
primes, under Assumptions 4.5–4.23). SQUFOF needs only an O(1)-sized queue on
average, so the collision version is worse on memory.

Other known failure modes: a period too short to contain an informative collision
(small regulator), and periods with no mixed collision. For the record, on the
single certificate N the first proper mixed collision closed at form 43. SQUFOF
found its square at F_18 and then took 8 reverse steps. N^{1/4}≈68.6. This is one
data point, not evidence.

## 6. Clean rejection-sampling cost: accepted, with root multiplicities

**General r.** Let r be the number of square roots of 1 among units. Then
r=2^{ω_odd(N)}·c₂, where c₂=1, 2, 4 for v₂(N)≤1, =2, ≥3 respectively. Every unit
square has exactly r roots, forming a coset of the 2-torsion. C5 checks this
exhaustively for N∈{15, 45, 105, 60, 120, 77}.

**Consequences.**
- Acceptance is rM/φ(N).
- Accepted squares are uniform on the M members of S. S may contain non-squares,
  which never hit.
- The ratio of two colliding roots is uniform over the r roots of 1. It is
  nontrivial with probability 1-2/r: 1/2 for an odd squarefree semiprime, as
  Card A says, 1-2^{1-k} for k odd primes, and 0 for odd prime powers.
- Raw cost is about φ/(r√M) for growing M. The minimum is about √(φ/r) at M=φ/r.
  This is order √φ for a semiprime, as stated. If M stays bounded, the cost is
  about φ.

**One sharper remark.** Drawing "uniform units" from [0,N) hits a non-unit with
probability 1-φ/N≈2/√N for a balanced semiprime. Over c√N draws, that trivial gcd
event already succeeds with constant probability. The sampler is therefore no
better than random trial gcd.

**Scope.** The bound covers this non-adaptive, uniform-root sampler with a
membership filter, nothing more. The CF walk shows the difference structured
acquisition makes: every sample lands in |Q|<2√N at O(1) cost, about N^{1/2}
cheaper per retained sample. That is exactly why CF-based methods reach a
heuristic N^{1/4}.

## 7. Exact missing computation and one materially different repair

**Missing.** A paid generator of norm-one relations λ=β/σ(β) whose β has *mixed*
ramified parity, at cost below the about N^{1/4} birthday on cycle coefficients.
Equivalently, a way to reach a nontrivial ambiguous form faster than walking a
cycle that has about √N distinct coefficient values. Card A's state space is one
deterministic cycle with no branching, so it cannot provide this. That is a
limitation of this design, not a lower bound for factoring.

**Repair: paid and materially different, but KNOWN prior art, so no gain.**
Move to the imaginary class group Cl(-4kN).
- Every class has a unique reduced form, so collisions are exact group equalities.
- Small prime forms f_ℓ give a Cayley graph with genuine branching. Under GRH its
  random walks mix rapidly (Jao–Miller–Venkatesan, an unaudited pointer).
- Acquisition is paid: √(-kN) mod small ℓ, then composition and reduction in
  poly(log N).
- Output: a group relation or element order, then 2-power reduction to an element
  of order 2, i.e. an ambiguous form (a,0,c) or (a,a,c). That gives a divisor of
  kN; the ambiguous forms coming from k, 2 and -1 must be excluded.

This is Shanks' class-group method. Schoof gives about N^{1/5+ε} under GRH, and
the Lenstra–Pomerance / Hafner–McCurley relation methods are subexponential. All
of these are unaudited pointers that were not read here. The repair removes Card
A's failed assumption (a single non-branching cycle), but at best it reproduces
known baselines.

## Disposition

- Accepted: the identities, the reverse-edge ±1 labels, the corrected update, the
  rejection-sampling cost with general r, and the ramified-sign lemma with its
  classification.
- Corrected: the "P' near √N" rule (it backtracks; the forward step is P'≈-√N).
- Rejected as stated: any implication that non-backtracking walks or residual
  cycles give useful roots by mixing.
- Mapping: exact G–W/CFRAC machinery.
- Best supported cost: none. Only the heuristic N^{1/4} analogy above, which
  gives no exponent gain and uses more memory.
- Next check that could change this: a *proved* frequency of mixed collisions per
  cycle, or a branching generator that is not already a known class-group
  algorithm. Re-running this certificate on more N would not.
