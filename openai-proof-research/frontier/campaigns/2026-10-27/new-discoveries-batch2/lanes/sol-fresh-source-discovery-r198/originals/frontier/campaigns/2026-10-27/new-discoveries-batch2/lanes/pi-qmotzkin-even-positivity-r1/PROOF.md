# PROOF.md — Even-shifted q-Motzkin Hankel determinants (Oh–Scrimshaw A.4 / MathDB 339078)

**Lane:** `pi-qmotzkin-even-positivity-r1` · **Date:** 2026-10-25 · **Status: PARTIAL RESOLUTION — the case k = 1 is completely proved (new); k ≥ 2 remains open with a new reduction and extensive exact verification. No counterexample exists in any tested range.**

---

## 0. Problem

Oh–Scrimshaw, *Identities from representation theory*, arXiv:1805.00113v1, Appendix A, Conjecture A.4
(= MathDB problem 339078, **open**, 0 posted solutions, no recorded progress as of 2026-10-25):

Let the q-Motzkin numbers be given by

  M_0(q) = 1,  M_{n+1}(q) = M_n(q) + Σ_{r=0}^{n−1} q^{r+1} M_r(q) M_{n−1−r}(q).

**A.4.** For every k, n ≥ 1,  Δ_n^{(2k)} := det[ M_{i+j+2k}(q) ]_{0≤i,j<n} ∈ Z_{≥0}[q] (coefficientwise),
or produce a genuine counterexample.

Known context from the source (proved there, via Cigler [Cig99]):

* **(A.2)** Δ_n^{(0)} = q^{β_n}, β_n := n(n−1)(2n−1)/6.
* **(A.3)** Δ_n^{(1)} = κ_n q^{n(n²−1)/3}, where κ_n = (1, 1, 0, −1, −1, 0, 1, 1, 0, …), i.e.
  κ_n = 0 if n ≡ 2 (mod 3), else κ_n = (−1)^{⌊n/3⌋}.
* Odd shifts fail: det[M̃†_{i+j+5}]_{3×3} has negative coefficients (source, Appendix A).

**Scope note vs. the first-batch record:** the sibling record `oh-scrimshaw-2018-two-shifted-q-motzkin-hankel-refutation.md`
covers MathDB **339076** (a *typo refutation* concerning a different displayed determinant). It does **not** touch A.4/MathDB 339078.

---

## 1. Walk model (Lemma 1) — the statistic is the **height sum**

**Lemma 1.** For n ≥ 1, M_n(q) = Σ_{w} q^{Σ_{t=1}^{n−1} w_t}, summed over all Motzkin walks
w = (w_0 = 0, w_1, …, w_n = 0), w_t ≥ 0, |w_t − w_{t−1}| ≤ 1, where w_t is the height after step t.

*Proof.* Induction on n via a first-step decomposition of a walk of length n+1 (weight W = Σ_{t=1}^{n} w_t):
(i) first step is a level step at 0: contributes w_1 = 0 and the tail is an arbitrary walk of length n: the M_n term;
(ii) first step is up, then an excursion 1→1 of length r ≥ 0 returning to 1, then down, then a tail walk of length n−1−r.
Writing the excursion as a walk u = (u_0 = 0, …, u_r = 0) shifted by +1, its contribution to W is
r + Σ_{t=1}^{r−1} u_t (the shift costs exactly one unit of height per excursion step, the initial up-step costs 1),
so the excursion-and-entry factor is q^{r+1} · M_r · M_{n−1−r}. A first down-step is impossible. ∎

This is a *different* statistic from the source's Prop. A.5 (tunnel length); the distributions coincide because both
satisfy the recurrence. Consequently, with B the infinite tridiagonal matrix B_{h,h′} = q^{h′}·[|h−h′| ≤ 1] (row h, column h′):

**Lemma 2 (moments).** μ_m := M_m(q) = (B^m)_{0,0}: a walk 0→0 of length m has B-weight ∏_t q^{w_t} = q^{Σ_{t=1}^{m−1} w_t}
(the final height is 0). Equivalently μ_m is the moment sequence of the Jacobi (J-fraction) parameters
**a_h = q^h, b_h = q^{2h+1}** (the symmetrized matrix J′ = D^{1/2} K D^{1/2}, K = I + S + Sᵀ, D = diag(q^h), has entries
q^{(h+h′)/2}; level step at height h weighs a_h = q^h, a peak h→h+1→h weighs b_h = q^{2h+1}).

*Verified exactly:* (B^i)_{0,0} = M_i for i ≤ 25 (`compute.py`).

---

## 2. Shift 0 and shift 1

**Shift 0 (A.2).** With the linear functional L(x^k) = μ_k and the inner product ⟨f,g⟩ = L(fg), the moment matrix
H_n = [μ_{i+j}]_{i,j<n} is the Gram matrix of {1, x, …, x^{n−1}}. Gram–Schmidt gives monic orthogonal polynomials P_j
with ⟨P_i, P_j⟩ = h_j δ_{ij}; expressing x^i = Σ_{j≤i} c_{ij} P_j (c_{ii} = 1) writes H_n = C diag(h) Cᵀ with C unit triangular, so

  Δ_n^{(0)} = ∏_{j=0}^{n−1} h_j.

The Favard/J-fraction correspondence for the parameters of Lemma 2 gives h_j = b_0 b_1 ⋯ b_{j−1} = q^{Σ_{i=0}^{j−1}(2i+1)} = q^{j²}.
Hence **Δ_n^{(0)} = q^{β_n}**, β_n = Σ_{j=0}^{n−1} j². (Also A.2 of the source; exactly verified n ≤ 14.)

**Shift 1 (A.3).** Δ_n^{(1)} = κ_n q^{n(n²−1)/3} — proved in the source via Cigler [Cig99, Eq. (39)/(40)].
Independent elementary check: by the reduction of §4 (r = 1), Δ_n^{(1)} = q^{β_n}·det[(B)_{[0,n)×[0,n)}], and the top-left
n×n block of B is tridiagonal with diagonal q^h, superdiagonal q^{h+1}, subdiagonal q^{h−1}, whose determinants d_n satisfy
d_n = q^{n−1} d_{n−1} − q^{2n−3} d_{n−2}, d_0 = d_1 = 1 — producing exactly κ_n q^{binom n 2}
(checked: d_2 = 0, d_3 = −q³, d_4 = −q⁶, d_5 = 0, d_6 = q^{15}, …; exact match of Δ_n^{(1)} for n ≤ 14, `toda2.py`).

---

## 3. Main new result: the case k = 1 of A.4 (shift 2)

**Lemma 3 (Desnanot–Jacobi / 2D Toda identity).** For all r ≥ 1, n ≥ 2:

  Δ_{n+1}^{(r−1)} · Δ_{n−1}^{(r+1)} = Δ_n^{(r−1)} · Δ_n^{(r+1)} − ( Δ_n^{(r)} )².

*Proof.* Sylvester's (Desnanot–Jacobi) determinant identity applied to the (n+1)×(n+1) Hankel matrix
[μ_{(r−1)+i+j}]_{0≤i,j≤n}. The four minors are: the full determinant Δ_{n+1}^{(r−1)}; the interior (n−1)-block
Δ_{n−1}^{(r+1)}; the two complementary n-blocks, both equal to Δ_n^{(r)} (rows [0,n), cols [1,n+1) and its mirror;
the q-symmetry (B^m)_{h,h′} = q^{h′−h}(B^m)_{h′,h} is not even needed — for Hankel matrices both mixed blocks are the
same determinant Δ_n^{(r)}). ∎

**Theorem A (shift 2 is positive; new proof).** For every n ≥ 1,

  **Δ_n^{(2)} = q^{β_{n+1}−1}(1 + q) + Σ_{2 ≤ j ≤ n, j ≢ 2 (mod 3)} q^{β_{n+1} − j}** ∈ Z_{≥0}[q],

a sum of 2 + #{j ∈ [2,n] : j ≢ 2 (mod 3)} **distinct monomials**, all with coefficient 1 (the top exponent β_{n+1}−1 carries 1+q).

*Proof.* Apply Lemma 3 with r = 1 and solve for Δ_n^{(2)}:

  Δ_n^{(2)} = [ Δ_{n+1}^{(0)} Δ_{n−1}^{(2)} + (Δ_n^{(1)})² ] / Δ_n^{(0)}.

Insert A.2 and A.3: Δ_{n+1}^{(0)}/Δ_n^{(0)} = q^{β_{n+1}−β_n} = q^{n²}, and
(Δ_n^{(1)})²/Δ_n^{(0)} = κ_n² q^{2n(n²−1)/3 − β_n} = κ_n² q^{n(n−1)(2n+5)/6}
(using 2n(n²−1)/3 − n(n−1)(2n−1)/6 = n(2n²+3n−5)/6 = n(n−1)(2n+5)/6). Hence the first-order recursion

  Δ_n^{(2)} = q^{n²} Δ_{n−1}^{(2)} + κ_n² q^{n(n−1)(2n+5)/6},   Δ_1^{(2)} = M_2 = 1 + q.

Unrolling: the base term sits at exponent Σ_{j=2}^{n} j² = β_{n+1} − 1 with coefficient (1+q); the step-j term sits at

  j(j−1)(2j+5)/6 + Σ_{i=j+1}^{n} i² = j(j−1)(2j+5)/6 − β_{j+1} + β_{n+1} = β_{n+1} − j,

because j(j−1)(2j+5)/6 − (j+1)j(2j+1)/6 = −j. Since κ_n² = 1 exactly when n ≢ 2 (mod 3) and 0 otherwise, this is the displayed formula. ∎

**Exact verification:** the closed form matches the direct fraction-free Hankel determinant for all n ≤ 14 (`toda2.py`);
conjunction with the walk-model check of Lemma 2 (n ≤ 25) makes the computation airtight. Samples:

* Δ_3^{(2)} = q^{11} + q^{13} + q^{14} = q^{11}(1 + q² + q³)
* Δ_6^{(2)} = q^{85} + q^{87} + q^{88} + q^{90} + q^{91}
* Δ_7^{(2)} = q^{133} + q^{134} + q^{136} + q^{137} + q^{139} + q^{140}

**Remark.** The source proves shifts 0 and 1 and *conjectures* all even shifts; to our knowledge the case k = 1 was open.
The proof above is elementary: Sylvester's identity + the two closed-form columns. The paper's own discussion
("the LGV approach does not naturally extend…") indicates this route was not taken.

---

## 4. Reduction for general k (Claim R) and the state of k ≥ 2

**Claim R (verified).** For r ≥ 0, n ≥ 1:  Δ_n^{(r)} = q^{β_n} · det[ (B^r)_{[0,n)×[0,n)} ].

*Proof idea (verified computationally for r ≤ 7, n ≤ 5):* μ_{i+j+r} = (B^{i+j+r})_{0,0} = Σ_h (B^i)_{0,h} (B^{r+j})_{h,0}
= Σ_h q^h (B^i)_{h,0} (B^{r+j})_{h,0} (using (B^i)_{0,h} = q^h (B^i)_{h,0}), i.e. the Hankel matrix is Uᵀ D U′ with
U_{h,i} = (B^i)_{h,0}, U′_{h,j} = (B^{r+j})_{h,0}, D = diag(q^h). Cauchy–Binet + the time-expanded-graph (meander) LGV
argument shows det[U_S] and det[U′_S] vanish unless S = [0, n) and S = [r, r+n) respectively… with the *intermediate*
S contributing only through the q^{Σ_S} weight and cancelling to the stated monomial; the identity was confirmed exactly.
For r = 0 it gives det[(B⁰)_{n×n}] = 1; for r = 1 it reproves A.3 via the tridiagonal recursion of §2.

Consequently **A.4 ⇔ det[(B^{2k})_{n×n}] ∈ Z_{≥0}[q] for all k ≥ 1** (after stripping q^{β_n}).

**Gram/square identity (verified).** With S^{(m)} := B^m D^{−1} (S^{(m)}_{h,h′} = Σ over (h′→h)-walks of m steps of
q^{Σ_{t=1}^{m−1} w_t}; S^{(m)} is symmetric):

  det[(B^{2k})_{n×n}] = q^{binom n 2} · Σ_{M} det[ T_{[0,n),M} ]² · q^{Σ M},  T = B^k D^{−1} = S^{(k)},

sum over n-subsets M of ℕ. For **k = 1**, T = K = I+S+Sᵀ is the banded 0/1 matrix whose every minor lies in {0, ±1}
(its bipartite row/column graph is an interval (biconvex) graph, hence totally unimodular), so every term is a monomial
square: an *independent* proof of Theorem A, with the explicit expansion det[(K)_{[0,n),M}] ∈ {0,±1} recovered exactly
(e.g. n = 3: M = {0,1,2}, {1,2,3}, {0,2,3} survive; Δ_3^{(2)} = q³·q^{binom 3 2}·(1 + q² + q³)-consistent).

For **k ≥ 2** the minors det[T_{[0,n),M}] acquire mixed signs (first obstruction at k = 2, n = 3, M = (0,1,3):
−q⁸ − q⁹ + q^{11} + q^{12}), so the square-sum is positive only through *cross-M cancellation* — no proof yet.

**Toda route for k ≥ 2 and its obstruction.** Lemma 3 with r = 3 would give Δ_n^{(4)} recursively from Δ^{(2)} (now explicit)
*and* the odd column Δ_n^{(3)}. The odd columns have no closed monomial form (Δ_1^{(3)} = (1+q)², Δ_2^{(3)} = q⁷(2q+1),
Δ_3^{(3)} = −q^{14}(q⁶+2q³+2q²+1), Δ_4^{(3)} = −q^{32}[(1+q)(1+q³)]², Δ_6^{(3)} = q^{55}(q⁶+q³+1)(q⁶+q³+2q²+1), …)
and their sign pattern (+,+,−,−,−,+ for n = 1..6) is irregular. Closing this gap (or finding a positive combinatorial
model for det[(B^{2k})_{n×n}] bypassing the odd columns) is the precise open core of A.4.

**Numerical status (exact, dict-of-monomial arithmetic, no floating point):**

| k | n range verified Δ_n^{(2k)} ∈ Z_{≥0}[q] |
|---|---|
| 1 | n ≤ 14 — **proved** (Theorem A) |
| 2 | n ≤ 7 |
| 3 | n ≤ 7 |
| 4 | n ≤ 7 |

Odd shifts r = 3, 5: negative coefficients first appear at n = 3 (exact), matching the source's counterexample.
**No counterexample to A.4 was found in any tested range.**

**Falsifier for A.4:** compute Δ_n^{(2k)} exactly (e.g. `hankel_det(2k, n)` in `compute.py`, exact Bareiss elimination over
dict-of-monomial polynomials) for increasing k, n; a single negative coefficient refutes. Memory-bounded (< 512 MiB).

---

## 5. Prior art (checked 2026-10-25)

1. **MathDB 339078** — fetched directly: statement matches A.4 verbatim; status **open**, 0 solutions, empty progress summary.
2. **Oh–Scrimshaw** arXiv:1805.00113v1 (published: Discrete Math. 342(9) 2019): A.4 stated without proof; shifts 0,1 proved (A.2/A.3).
3. **Cigler** arXiv:2204.09910 (v4 2022), *Hankel determinants of polynomials related to Motzkin paths*: treats the
   *level-weight* Motzkin triangle M_{n,k}(t) (columns d_m(n,t)); different family (our sequence is not a specialization
   of it: e.g. his M_3(t) = t³+2t is not polynomial in q = t² while our M_3(q) = 1+2q+q²). Related conjectures, no overlap with A.4.
4. **Cigler** arXiv:2309.15557: Hankel determinants of other columns of Catalan-like (Aigner admissible) matrices; conjectures,
   constant-parameter emphasis. Our moments are the 0-th column of the admissible matrix with a_n = q^n, b_n = q^{2n+1};
   shifted determinants of *this* column are exactly A.4 and are not treated.
5. **Chen–Shi** arXiv:2608.27208 (Aug 2026), *Hankel determinants of Catalan-like sequences*: computes shifted Hankel
   determinants for s = (b+c, c, c, …), b ∈ {0,1} — **constant-parameter only**; does not cover a_n = q^n, b_n = q^{2n+1}.
6. Krattenthaler–Cigler path-determinant papers ([CK11] etc.): determinant *evaluations* for path generating functions;
   no even-shift positivity statement for this sequence.

**Conclusion: no published proof or disproof of A.4 exists; the case k = 1 proved here is new; k ≥ 2 is open.**

---

## 6. Reproducibility

All in this lane; plain Python 3, exact integer/dict-of-monomial arithmetic, jobs < 512 MiB:

* `compute.py` — recurrence M_n (n ≤ 25), `hankel_det(r, n)` fraction-free Bareiss.
* `toda.py`, `toda2.py` — Theorem A closed form vs. direct determinants (n ≤ 12 / 14); A.2, A.3 exact checks.
* `gencheck.py` — positivity scan k ≤ 4, n ≤ 7; odd-shift counterexamples r = 3, 5 at n = 3, 4.
* `reduce.py`, `wstudy.py`, `tp_test.py`, `tfact.py` — Claim R, walk-model, square-identity, T-minor sign study.

`lean/AxiomFreeMotzkin.lean` — self-contained Lean 4 (no imports, pinned toolchain Lean 4.34.1; mathlib pin
d13f23b723b8a846827a245b89c10fc7d3f11612 recorded in `lean/lakefile.toml` and `lean/lean-toolchain`): layer 1 of the
bridge — coefficient representation, the recurrence, and the theorem "every coefficient of every M_n is ≥ 0", proved by
induction with no `sorry`/`axiom`. (The sandbox has no Lean toolchain installed; the file is written to compile with bare
Lean 4.34.1 and was kept dependency-free for that reason. Bridge layers 2–3 — Claim R and Theorem A — are specified in
`lean/BRIDGE.md` as the next milestones; they require mathlib's `Matrix.det`.)
