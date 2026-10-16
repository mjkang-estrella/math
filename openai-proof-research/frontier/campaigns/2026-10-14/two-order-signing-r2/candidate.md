# Two prescribed orders, round 2: the scalar core of T2 is an open weighted-discrepancy problem

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0;
original code MIT. Third-party material keeps its own rights.

**Disposition: UNRESOLVED.** The full target T2 is neither proved nor refuted.
Nothing here is nominated as a substantial result, and nothing is counted.
The computations are the author's own finite checks. They are not
independent reviews.

The main new finding is a status result. Already in dimension one, T2 is
exactly equivalent (up to a factor 2 in the constant) to the following
question: does every weighted *one-block* 0-1 matrix have bounded
discrepancy? Cherniavskii, Kupavskii, Moiseev and Shekhovtsov posed this
question as open in arXiv:2610.16079v1, §6 (12 October 2026). It is also
exactly the boundedness of the "weighted two permutation discrepancy" of
Bansal, Rohwedder and Svensson (STOC 2022, Definition 19). Reis's 2023
weighted-discrepancy conjecture (in either of its stated forms) implies it.
Bérczi, Liu, Reis and Tarnawski's 2026 prefix-constrained basis conjecture
also implies it. So a proof of T2 would settle a recently posed open problem,
and a counterexample to T2, even at d=1, would refute two published
conjectures. The pinned one-order theorem gives nothing beyond greedy in d=1.
The missing step is therefore the coupling of the two orders, not the
dimension.

## 1. Target, scope and inherited state

The target T2 is unchanged from `inputs/private/context/r4/original-scope.md`:

> There exists an absolute finite C such that, for every d,N ≥ 1, every
> v_1,…,v_N ∈ R^d with ||v_i||_2 ≤ 1 and every pi,rho ∈ Sym([N]), there is one
> epsilon ∈ {−1,1}^N satisfying
>
>     max_{sigma ∈ {pi,rho}, 0 ≤ k ≤ N}
>         || Σ_{j=1}^k epsilon_{sigma(j)} v_{sigma(j)} ||_2 ≤ C sqrt(d).

No restriction is placed on orders, coordinate signs, dimension, palettes,
zero sums or norms. Both orders use the same signs. The bound must not depend
on N. See `original-scope.md` in this directory.

The frozen r4 package was authenticated before use. Its `seal.json` has SHA256
`e1cda9940e5020d9e47fe6e8a8e2124e7a643b8bc3e8560beee55c55f9c0ab2d`, which
matches the handoff. Its read-only verifier returned
`PASS_integrity_and_finite_support_only` with 70 authenticated files and
11 pinned blobs, and it wrote nothing. Copies of that seal, both of its
manifests, its report and its scope are bound in this round's input manifest.
`verify.py` re-checks that the copied seal has the handoff hash. It then checks
that the copied manifests match that seal, and that the copied report, scope
and Reis-thesis extraction match their r4 manifest entries.

The r4 report proves three method obstructions. (i) Sharing one coefficient
vector between forward and reverse source feedback is inconsistent for even N.
(ii) Raw prefix bodies have Dirichlet energy that grows logarithmically.
(iii) Adding odd/even-order constraints to a fixed forward filter also has
diverging energy. These are limits of particular constructions, not failures
of T2. The scalar reversal and odd/even examples have bounded common signings.
All of this is retained and is not repeated here as evidence against T2.

## 2. Notation

For d ≥ 1 let B^d be the closed Euclidean unit ball. All suprema below are
taken in [0,∞].

* **Two-order constant.**
  D_2(d) := sup_{N, pi, rho, v ∈ (B^d)^N} min_epsilon max_{sigma,k} ||Σ_{j≤k} epsilon_{sigma(j)} v_{sigma(j)}||.
  T2 says exactly that D_2(d) ≤ C sqrt(d) for all d.
* **Interval-coverage constant.** For finitely many closed bounded intervals
  I_1,…,I_N ⊂ R with vectors v_j ∈ B^d, put
  cov_epsilon(x) := Σ_{j : x ∈ I_j} epsilon_j v_j. Then
  D_I(d) := sup min_epsilon sup_{x∈R} ||cov_epsilon(x)||.
* **One-block constant.** Fix a row order of a 0-1 matrix M. M is *one-block*
  if the ones in every column form one consecutive block of rows. Put
  D_OB(d) := sup over one-block M (m×N) and v ∈ (B^d)^N of
  min_epsilon max_r ||Σ_j M_rj epsilon_j v_j||.

When d=1, put d_j := |v_j| ∈ [0,1] and absorb sign(v_j) into epsilon_j.
Then D_OB(1) is exactly the supremum, over 0-1 one-block matrices A, of
wdisc(A) := sup_{W diagonal in [0,1]} disc(AW). Reis, Chapter 8, uses this
notion. Likewise, D_2(1) is exactly the supremum over n of the "weighted two
permutation discrepancy" C_n in BRS Definition 19, where the first order is
the identity. Relabeling the indices makes this no loss.

## 3. Exact interval reformulation (new to this project; elementary)

**Theorem 1.** For every d ≥ 1,

    D_2(d) ≤ D_OB(d) ≤ 2 D_2(d)    and    D_2(d) ≤ D_I(d) ≤ 2 D_2(d).

So T2 holds iff D_I(d) = O(sqrt d) iff D_OB(d) = O(sqrt d). In particular,
the d=1 case of T2 holds iff weighted one-block 0-1 matrices have uniformly
bounded weighted discrepancy.

*Proof.* (a) *Two orders embed as intervals.* Fix pi, rho and v. Let
a_i := pi^{-1}(i) and b_i := rho^{-1}(i), both in [N]. Put
I_i := [a_i, 2N+1−b_i]. This interval is nonempty because a_i ≤ N < N+1 ≤ 2N+1−b_i.

* For an integer x=k with 1 ≤ k ≤ N, x ∈ I_i iff a_i ≤ k. The upper
  condition k ≤ 2N+1−b_i always holds. So cov_epsilon(k) is the k-th pi-prefix.
* For x = 2N+1−k with 1 ≤ k ≤ N, the condition a_i ≤ x always holds, and
  x ≤ 2N+1−b_i iff b_i ≤ k. So cov_epsilon(x) is the k-th rho-prefix.
* The empty prefixes are zero.

Hence, for every epsilon, the two-order maximum is at most
sup_x ||cov_epsilon(x)||, and the minimum over epsilon gives D_2 ≤ D_I.
Restricting to the integer points 1,…,2N gives the 2N×N matrix whose rows,
in order, are P_1,…,P_N, Q_N,…,Q_1. Here P_k and Q_k are the k-th pi- and
rho-prefix sets. Column i has ones exactly in rows a_i,…,2N+1−b_i, which is
one block. The same signs therefore give D_2 ≤ D_OB.

(b) *Intervals reduce to two orders.* Take closed intervals I_j = [l_j, r_j]
with l_j ≤ r_j. Let sigma_L order the indices by (l_j, j) and sigma_R by (r_j, j).
For each x define L(x) := {j : l_j ≤ x} and R(x) := {j : r_j < x}.

* L(x) is an initial segment of sigma_L, because any index with smaller
  l also lies in L(x).
* R(x) is an initial segment of sigma_R, for the same reason.
* R(x) ⊆ L(x), because l_j ≤ r_j < x.
* {j : x ∈ I_j} = L(x) \ R(x).

Therefore cov_epsilon(x) = S_L(x) − S_R(x), where S_L(x) and S_R(x) are
prefix sums of epsilon_j v_j in the orders sigma_L and sigma_R. Signing this
two-order instance within D_2(d) + eta, for any eta > 0, makes every coverage
value at most 2(D_2(d) + eta). Letting eta → 0 gives D_I ≤ 2 D_2.

For a one-block matrix, the same argument applies to the integer intervals
{s_j,…,t_j} of row indices. An all-zero column is placed last in both orders.
It never lies in L(r) or R(r), so it does not change the coverage. This gives
D_OB ≤ 2 D_2. ∎

Finite exact checks of both directions are in `checks.py` (A1–A3, with a
deliberate off-by-one control in C).

**Corollary 2 (literature identification at d=1).** All primary statements
below were read at the extents listed in `source-contracts.md`.

1. In BRS Definition 19, C_n is the best bound for real values in [−1,1],
   the identity order and a second permutation sigma. Then sup_n C_n = D_2(1).
   BRS bound C_n only when all entries are in {−1,0,1} (bound 4, Theorem 20
   with Lemma 17). They give evidence that the weighted variant is "much
   harder" (§5.3, Lemma 21).
2. CKMS §6 ("Weighted one-block matrices") asks whether every A_ij = d_j 1[i ∈ I_j]
   with d_j ∈ [0,1] has constant hereditary discrepancy. Restricting the columns
   of such an A gives another matrix of the same kind. So the question asks
   whether D_OB(1) < ∞, which by Theorem 1 holds iff D_2(1) < ∞ (the d=1 case
   of T2). CKMS state that this special case of Reis's conjecture remains a
   question, and they ask for a direct proof.
3. Reis's Conjecture 16 says wdisc(A) < 2 herdisc(A) for every real matrix.
   Two-permutation prefix matrices are TU with herdisc ≤ 1 (Reis, Chapter 8),
   so this conjecture would give D_2(1) ≤ 2. The O(1)·herdisc form quoted by
   CKMS would give D_2(1) < ∞.
4. Reis's Theorem 142 (proof via Claim 143, read in full) gives two-permutation
   instances with value (2k+2)/(k+2). Hence D_2(1) ≥ 2, so the T2 constant
   satisfies C ≥ 2. Check R replays the stated values exactly for k ≤ 4; the
   general k is Reis's proof.

**Proposition 3 (prefix-constrained bases imply the scalar core).** Suppose
Bérczi–Liu–Reis–Tarnawski's Conjecture 5 holds with constant C. That is, for
every matroid M on [n], every w ≥ 0 and every x in the base polytope, some
basis B satisfies |Σ_{i≤t} w_i(1_B(i) − x_i)| ≤ C max w for all t. Then
D_2(1) ≤ 4C.

*Proof.* Take scalars v_1,…,v_N ∈ [−1,1] and orders pi, rho.

* Let the ground set be {i^+, i^- : i ∈ [N]}, ordered as
  pi(1)^+,…,pi(N)^+, rho(1)^-,…,rho(N)^-.
* Let M be the partition matroid that chooses exactly one element of each
  pair {i^+, i^-}. The point x ≡ 1/2 lies in its base polytope.
* Give both copies of i the weight w(i^±) := |v_i| ≤ 1.
* Take the basis B from Conjecture 5 and set delta_i := +1 if i^+ ∈ B and
  −1 otherwise.

Then 1_B(i^+) − 1/2 = delta_i/2 and 1_B(i^-) − 1/2 = −delta_i/2. The t=k
prefix (k ≤ N) equals (1/2) Σ_{j≤k} |v_{pi(j)}| delta_{pi(j)}, so every
pi-prefix has absolute value at most 2C. The t=N+k prefix equals

    (1/2) Σ_all |v_i| delta_i − (1/2) Σ_{j≤k} |v_{rho(j)}| delta_{rho(j)}.

The first term is the full pi-prefix, so every rho-prefix has absolute value
at most 4C. Finally, epsilon_i := delta_i sign(v_i) with sign(0) := 1. ∎

Check M replays both identities and the derived 2E/4E bounds exactly. A
wrong-sign control is also detected. By the same embedding, Bérczi et al.'s
unconditional Theorem 14 would give D_2(1, N) = O(log N). This consequence is
recorded for context only and is not used.

**Consequences for the campaign.**

* A proof of T2 would in particular answer the CKMS question affirmatively,
  and with it BRS's weighted two-permutation question.
* A counterexample to T2 already at d=1 would refute the O(1) form of Reis's
  conjecture for 0-1 one-block (TU) matrices, and Bérczi et al.'s Conjecture 5.

This report does not claim either outcome. These identifications show that T2
contains, as its d=1 case, a problem that experts posed as open in October
2026. That problem was earlier singled out by Reis as the harder TU case,
where only lower bounds are given.

## 4. Where the difficulty lives

**Remark 4 (d=1 one-order is greedy).** For one order and scalars in [−1,1],
choose each sign opposite to the current prefix sum, using +1 at zero. Every
prefix then stays in [−1,1]. The induction step is |s − |v|| ≤ 1 when
s ∈ [0,1] and |v| ≤ 1, and symmetrically. So at d=1 the pinned one-order
theorem `thm:signing` adds nothing beyond this greedy bound. Yet the d=1
two-order problem is exactly the open question of Corollary 2.

This shows where the gap lies. The source's analytic machinery (filtered
Dirichlet energies, adaptive shifts, Gaussian path correlation) is what turns
O(d) into O(sqrt d) for one order. The missing step in T2 is the coupling of
two orders, and that step is already unresolved when d=1. Any proof of T2
must therefore contain a new argument for weighted one-block matrices. This
is a statement about content, not a theorem that excludes particular proof
methods.

**Remark 5 (norm classes are without loss).** Suppose T2 holds with constant
C' for families whose norms all lie in (1/2,1] ∪ {0}. Then T2 holds with 2C'.

*Proof.* Split the indices into U_b := {i : 2^{-b-1} < ||v_i|| ≤ 2^{-b}} for
b ≥ 0. Only finitely many classes are nonempty, and zero vectors get any sign.
Sign the rescaled family 2^b v_i, i ∈ U_b, in the two orders restricted to
U_b. Each prefix of pi or rho meets U_b in a prefix of the restricted order.
So each class contributes at most 2^{-b} C' sqrt d, and the classes sum to at
most 2C' sqrt d. ∎

So making all norms comparable is no restriction. In particular, the scalar
core is equivalent to its case with weights in (1/2,1]. The hard regime is
many distinct but comparable weights. With finitely many distinct weights
a_1 > … > a_K, signing each weight class by the unweighted two-permutation
bound (1, BRS §5 and the Bansal–Nikolov survey §2.3) gives at most Σ a_k.
That bound is not uniform in K.

## 5. Unconditional baseline over the full scope

This is a standard linear-algebraic bound. It adapts Bansal–Nikolov,
*Discrepancy Theory: An Algorithmic and Geometric Perspective*, Theorem 2.8
(k permutations, scalar), to vectors. The proof is self-contained and is
included so that the round has an honest unconditional bound over all
quantifiers. It is not a resolution, because it grows with N.

**Lemma 6.** Let x ∈ [−1,1]^N, let A := {i : |x_i| < 1}, and let
Lambda : R^A → R^q be linear. Put

    Q := {y ∈ [−1,1]^N : y_i = x_i for i ∉ A, Lambda(y_A − x_A) = 0}.

Then Q is a nonempty polytope, and each vertex y of Q has at least
|A| − rank(Lambda) indices i ∈ A with |y_i| = 1.

*Proof.* Q contains x and is bounded. Let K := {z ∈ R^N : z_i = 0 off A,
Lambda z_A = 0}, so dim K = |A| − rank(Lambda) =: k. Let T ⊆ A be the set of
coordinates of A that are tight at y. If some nonzero z ∈ K has z_T = 0, then
y ± tz ∈ Q for small t > 0, since the coordinates of A outside T have slack.
That would contradict y being a vertex. Hence K ∩ {z_T = 0} = {0}, and this
subspace has dimension at least k − |T|. So |T| ≥ k. ∎

**Proposition 7 (baseline).** For all d,N, every v ∈ (B^d)^N and every pi,rho,
some epsilon has every prefix in both orders of norm at most
(8d − 2)(⌊log2 N⌋ + 1).

*Proof.* Start with x^(0) = 0 and put g := 4d. Phase t runs while
A_t := {i : |x^(t−1)_i| < 1} is nonempty. It does the following.

* For each sigma ∈ {pi,rho}, list A_t in sigma-order and cut the list into
  consecutive groups of exactly g indices. Any shorter tail is left unconstrained.
* For each complete group G, impose the d scalar equations
  Σ_{i∈G}(y_i − x_i) v_i = 0.
* There are at most 2⌊|A_t|/g⌋ d ≤ |A_t|/2 equations. Let x^(t) be a vertex
  of the resulting Q.

By Lemma 6, at least |A_t|/2 coordinates of A_t become tight, so
|A_{t+1}| ≤ |A_t|/2. Hence |A_t| ≤ N/2^{t−1}, and the process stops after
T ≤ ⌊log2 N⌋+1 phases. The final x^(T) is a sign vector epsilon.

Now fix a sigma-prefix S. In phase t, only coordinates in A_t move.
S ∩ A_t is an initial segment of the active sigma-list. It is therefore a union
of complete groups, which preserve their weighted sum, together with fewer
than g further indices. Each coordinate moves by at most 2 and each
||v_i|| ≤ 1, so the prefix sum changes by at most 2(g−1) = 8d − 2 per phase.
Summing over the phases, starting from 0, gives the bound. ∎

Check B runs this exact algorithm in rational arithmetic, with d ≤ 3 and
N ≤ 40. It checks the equation count, the halving, the per-phase prefix
change and the final bound. This bound is O(d log N). T2 asks for O(sqrt d)
uniformly in N. CKMS Theorem 4 (statement read, proof not used) gives an
O(log)-type bound for weighted one-block matrices at d=1.

## 6. Mechanisms tried in this round, and where each fails

These are honest attempts at the scalar core. None of them closes the gap.
Each item records exactly where the attempt fails. Proved statements are
marked as proved; anything else is labeled heuristic or numerical.

1. **Bit-level decomposition (failed).** Write |v_i| = Σ_b beta_ib 2^{-b} and
   U_b := {i : beta_ib = 1}. If the signs satisfy |Σ_{i ∈ P ∩ U_b} epsilon_i| ≤ D_b
   for every pi- and rho-prefix P, with Σ_b 2^{-b} D_b ≤ C', then the scalar
   core holds with C'. This step is proved by the triangle inequality. The
   conditions form a system of 2(B+1) restricted prefix chains with one
   common signing. For three or more unrelated chains, unweighted discrepancy
   can be Ω(log n) (Newman–Neiman–Nikolov, as cited by CKMS Theorem 5). The
   level-b chains are not unrelated, since they restrict the same two
   permutations, but no structure was found that removes the coupling across
   levels. The geometric allowances D_b do not help at levels 0 and 1, which
   need constants. The LSV-type bit rounding cannot be used, because it needs
   independent signs at each bit level, while T2 needs one sign per index.
2. **Weighted pairing and merging (failed).** BRS Lemma 17 and survey §2.3
   use consecutive pairs in both orders. Reis's Theorem 141 merges
   weight-sorted pairs. With weights, opposite signs inside a pair leave the
   residual w_a − w_b, and the union of the two matchings ties all residual
   orientations on a cycle to one bit. The residual problem is a signing of
   cycles whose contributions are spread over both orders. It is not a
   smaller instance of the same kind, and no recursion was found in which the
   residuals shrink.
3. **Robust online game (closed in the literature).** BRS Theorem 20 shows
   that a robust constant-bound maker strategy for the one-dimensional game
   would bound D_2(1). BRS Lemma 21, whose proof was read in full, gives
   instances with values in [1/2,1] where the breaker forces
   Ω(log n / log log n). So this sufficient route cannot give a constant.
4. **Iterated rounding (logarithmic loss).** Proposition 7 loses a constant
   in each of log N phases. The Beck–Fiala alternative also fails. That
   alternative would drop a prefix row once at most t of its active
   elements are still fractional. Within one chain, the rows that still
   contain more than t fractional elements, restricted to the fractional set
   F, are |F|−t distinct nested nonempty sets. Such sets are linearly
   independent (proved). With two chains, the kept rows can therefore have
   rank |F| once |F| ≥ 2t, for example whenever the second chain adds a
   single independent row. Then no free direction remains. Some other
   accounting is needed to avoid paying in every phase.
5. **Relaxations (numerical only).** The semidefinite (vector-coloring)
   relaxation was solved with CLARABEL in exploratory scripts. On random and
   bit-reversal two-order instances with N ≤ 128, and in weight-climbing
   searches with N = 12 and 24, its value never exceeded 1. So no SDP-dual
   certificate of a large lower bound appeared at these sizes. This is
   numerical evidence, not a theorem; boundedness of the relaxation was not
   proved. For one order, BRS §6 proves SDP prefix discrepancy at most 1 via
   Banaszczyk. Their argument needs a one-order prefix theorem, and no
   two-order analogue is available.
6. **Small exact values (numerical search; one exact check).** Weight
   hill-climbing and an exact cutting-plane minimax with MILP inner solves
   (HiGHS) never found a two-order scalar instance with value ≥ 2 for N ≤ 21.
   The cutting-plane search certified the maximum over weights for Reis's
   k=3 orders as 5/3, at weights (1,5/6,1,5/6,1,2/3,1). Check E verifies this
   value exactly. That is above Reis's 8/5 for the same N but below his
   limiting lower bound 2. These searches say nothing about large N.
7. **Lifting two orders into one order (not achieved).** A route through the
   pinned theorem would need each rho-prefix to be a bounded combination of
   one-order prefix functionals of lifted vectors in O(d) dimensions with
   O(1) norms. The interval form of Theorem 1 shows what is needed:
   cov(x) = S_L(x) − S_R(x) is one *arrival* prefix minus one *departure*
   prefix, and the departures follow a second, unrelated order. No bounded
   encoding was found. Arbitrary encodings were not proved impossible.
8. **Source filter route (not retried).** The r4 obstructions are retained.
   Remark 4 explains why that route alone cannot reach the d=1 coupling.

## 7. Exact unpaid step

T2 is equivalent to the conjunction of two statements.

* **(U1) Scalar coupling.** D_I(1) < ∞. That is, finitely many closed
  intervals with weights in [0,1] always admit a signing whose signed
  coverage is bounded by an absolute constant at every point. Equivalently,
  D_2(1) < ∞. This is the open CKMS §6 / BRS Definition 19 question, implied
  by Reis's Conjecture 16 and Bérczi et al.'s Conjecture 5. The best
  unconditional bound used here is O(log N) (Proposition 7 at d=1).
* **(U2) Dimension.** D_2(d) = O(sqrt d) for all d. No reduction from (U2)
  to (U1) is known to this report. The pinned theorem pays the dimension
  only for one order.

T2 implies (U1). This round does not prove (U1), (U2), any intersection of
the two feasible sign sets, or any counterexample. No step is assumed or
hidden. The target was not narrowed, and no restricted case is presented as
success.

## 8. Contribution assessment

* Theorem 1 is a short, elementary reformulation. It is probably known to
  specialists in some form, although no source read here states it.
* Proposition 3 is a two-line embedding.
* Proposition 7 is standard.

None of these is a substantial or nonroutine advance, and none is nominated.
Their value is diagnostic: T2 is not a credible "completable gap" for the
ten-results campaign. Its d=1 core was posed as open in October 2026, after
being singled out in 2022 and 2023, and its natural game approach is
provably blocked. The recommendation to the parent is to retire T2 as a
nomination target unless a genuinely new mechanism for weighted interval
coverage appears. A disproof would also be welcome, but none is in sight:
the SDP relaxation numerically gives no lower-bound certificate.

## 9. Files, checks and provenance

* `checks.py`: standard library only, exact rationals, fixed seed. It runs
  checks A1–A3, M, B, R, E and the negative controls C. Its stdout is stored
  byte-for-byte in `checks-receipt.txt`.
* `verify.py`: authenticates the detached seal, both inventories, every file
  hash and size, and the r4 chain, before it replays anything. It then
  compares the fresh stdout with the receipt. It writes nothing and uses no
  network.
* `mutation_tests.py`: optional rejection tests on disposable copies.
* `exploration/`: the numerical scripts (numpy/scipy/cvxpy) and logs for
  §6 item 5 and the search part of §6 item 6. They are not part of the
  verified replay, and no proof depends on them.
* `source-contracts.md` and `literature-screen.md`: exact URLs, hashes,
  reading extents and queries.
* Third-party copies are under `inputs/private/` and are not release artifacts.
