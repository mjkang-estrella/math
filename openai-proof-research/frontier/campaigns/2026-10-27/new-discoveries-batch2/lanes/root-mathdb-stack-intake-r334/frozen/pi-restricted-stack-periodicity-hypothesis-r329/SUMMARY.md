# SUMMARY — MathDB 347483 (pi-restricted-stack-periodicity-hypothesis-r329)

**Target.** Berlow, "Restricted Stacks as Functions", arXiv:2008.01164v2, Conjecture 5.1
(published Discrete Math. 344 (2021) 112571, DOI 10.1016/j.disc.2021.112571): *the only
periodic points of s_{132,213} and s_{231,213} are the identity and its reverse* — for every
n and every π ∈ S_n, π is periodic under the respective map iff π ∈ {id_n, rev_n}.
Provisional r320 triage lead; source/prior clearance was assigned to this lane as first task.

**Disposition: UNRESOLVED — PARKED with precise missing lemma.** No counterexample exists
for n ≤ 10 (full exhaustive certification, both maps). No all-n proof obtained. The target is
genuinely open in the literature as of 2026-10-31.

## 1. Source and scope clearance

- Primary definitions read top-to-bottom from the retained arXiv v2 body (Def 1.2 patterns,
  Def 1.3 s_T with top-to-bottom stack reading and input retry, Def 2.1/2.2 clumping,
  Def 4.1 periodic point, Def 4.2 half-decreasing, Thms 1.5/2.3/3.2, Lemmas 4.3/4.4,
  Thm 4.5, Cors 4.6/4.7/4.9, Conjecture 5.1). Frozen input hashes in `frozen/SHA256SUMS.frozen`;
  fresh re-download of both primary files is **byte-identical** to the r320 frozen copies
  (2008.01164v2.html sha256 7a05e4198c96…, abs 5a9d72fb13c2…), independently re-confirming
  provenance at 2026-10-31T00:39:29Z.
- Semantics pinned independently: the stack word is read **top-to-bottom** and must avoid
  **T** (not T^r). Verified against five proved results of the source (V1–V7 below), 17/17 pass.
- Prior art (bounded but real pass): **arXiv:2405.01854 (Zhang 2024, pub. ECA 5:3 2025)
  restates the conjecture as OPEN** (its Conjecture 4.2, extended to (213,231),(132,213),(231,312)).
  Seidel–Sun (arXiv:2308.05868, Disc. Math 349 (2025) 114947) concerns consecutive-pattern
  maps SC_σ — different map. Mi–Xu–Yang (ECA 5:3 #S2R22, 2025, s_{(T,k)} for T={12,21})
  contains no periodic-point result for the target pairs (verified: zero "periodic" matches
  in the retained full text). Vatter's Feb 2026 problems survey (arXiv:2602.16355) does not
  mention it; citation trail of 2405.01854 shows no resolution. Bao–Cerbai–Choi–Gan–Zhang
  (Ann. Comb. 2024) concerns σ-machines. **No resolution found as of 2026-10-31.**
  Caveat: the published Elsevier wording of Conjecture 5.1 was NOT compared (ScienceDirect
  is access-blocked per policy); arXiv v2 is the retained primary of record.
- Scope vs r304: zero matches for "347483"/"Berlow" in accepted-exclusions.json and
  historical-dispositions.json — no overlap, no double-count risk.

## 2. Proved lemmas (this lane; machine-checked on stated ranges, proofs below)

**Lemma A (2-cycle, all n).** For T ∈ {{132,213},{231,213}}: s_T(id_n)=rev_n and
s_T(rev_n)=id_n. *Proof.* id_n: every push keeps the stack word top-to-bottom a decreasing
word (all triples 321-type), which avoids T; dump gives rev_n. rev_n: stack word increasing
(all triples 123-type), avoids T; dump gives id_n. Verified computationally n ≤ 10. ∎

**Lemma B (reversal tightness; all n).** If π avoids T ∪ T^r then s_T(π)=π^r and
s_T(π^r)=π, so {π, π^r} is a 2-cycle. For both target T's,
T ∪ T^r = {132,213,231,312} and Av_n({132,213,231,312}) = {id_n, rev_n}.
*Proof.* First claim: π avoids T^r ⟹ every prefix of π^r avoids T (an occurrence of σ∈T in
π(j)…π(1) reverses to an occurrence of σ^r ∈ T^r in π), so all pushes succeed and Thm 2.3
gives s(π)=π^r; and π^r avoids T^r iff π avoids T. Second claim: a {132,213,231,312}-avoider
has every triple monotone; consecutive triples share orientation, hence π is monotone.
**Consequence: the pure-reversal mechanism produces no periodic points beyond {id,rev} — the
"easy counterexample family" is provably empty.** ∎ (Cross-checked: the same set
Av(T ∪ T^r) = {id,rev} is exactly the periodic-point set of Seidel–Sun's Theorem 1.1 for the
consecutive map SC_σ with σ ∈ {132,213} — consistent structure, different map.)

**Lemma C (last element; all n, both maps).** (s_T(π))_n = π_1. *Proof.* The bottom stack
element π_1 can be popped only while a blocked push persists with stack = {π_1}, impossible
since a violation needs 3 stack elements. Hence π_1 is popped last. Verified on S_3..S_7. ∎
(Note: this does NOT force π_1 = π_n on a cycle — s^k(π)_n = s^{k-1}(π)_1, which is a
statement about predecessor cycle elements, so no cheap domain restriction for large n.)

**Theorem D (finite certification; n ≤ 10, both maps).** For every π ∈ S_n, n ≤ 10:
s_T^k(π) ∈ {id_n, rev_n} for some k ≤ B(n), where max hitting B(n) is
- s_{132,213}: n=3:3, 4:4, 5:7, 6:7, 7:12, 8:13, 9:18, 10:21;
- s_{231,213}: exactly n−1 (2,3,4,5,6,7,8,9 for n=3..10).
Certificate logic: if every orbit hits {id,rev} within B(n), any cycle C meets {id,rev}
(orbit of a cycle member stays in C), hence C = orbit of id = {id,rev}; so periodic points
are exactly {id,rev}. Full sweeps of S_n (n ≤ 9 in one guarded run each; n = 10 in five
chunks partitioned by π(1) mod 5, counts 725759/725760 summing to 10!), CAP=200, zero flags.
**This is a complete, independently implemented, source-faithful resolution of the exact
question for all n ≤ 10 — superseding the unreviewed r320 n ≤ 8 diagnostics** (which my
results confirm).

**Theorem E (reduction).** Conjecture 5.1 ⟺ **Attractor Lemma**: for all n and all
π ∈ S_n, some iterate s_T^k(π) ∈ {id_n, rev_n} (k ≥ 0). (⇐ by Theorem-D argument;
⇒ trivial since {id,rev} is the cycle.) So the open content is exactly the Attractor Lemma.

## 3. Mechanism 2 (structure) — what was sustained, where it obstructs

- **Exact push-blocking condition** (derived and machine-verified). Map A ({132,213}):
  push x onto stack word w_1…w_m (top-to-bottom) blocked iff ∃ i<j with
  (x < w_j < w_i) or (w_i < x < w_j). Map B ({231,213}): blocked iff ∃ i<j with w_i > w_j
  and x < w_i. These give exact recurrences.
- **Theorem 2.3 clumping recurrence verified against direct simulation on all of S_6 for
  both maps** (checks/recurrence_check.py): s_T(π) = rev(π[i₂..i₃−1]) · s_T(π ∖ [i₂..i₃−1]),
  (i₁,i₂,i₃) = colex-least (min i₃, then i₂, then i₁) occurrence of T^r in π. This is the
  correct recursive handle; an earlier r-conjugation guess (s_{T^r} = r∘s_T∘r) is FALSE
  (LIFO asymmetry) — falsified on S_5; complement conjugation s_{c(T)} = c∘s_T∘c holds.
- **No scalar Lyapunov function** among inv, noninv, disp, disp², desc, maj, LIS, LDS:
  none is monotone along off-cycle edges (work/lyapunov-scan.json, S_5–S_6). Map B shows
  exact inv balance (dec=inc), suggesting a hidden involution symmetry, not a monotone potential.
- **Structural mechanism visible in data (map B, π₁ = n case, proved by hand):** if π₁ = n,
  n lodges at the stack bottom; the machine then outputs, for each input x in order, the
  elements of the current top part smaller than x (in increasing order), pushes x, and dumps
  increasing + n; s_B(6,1,2,3,5,4) = id illustrates. This suggests an induction through
  "settled" elements, but the general case (n not first, n popped mid-run) resists the
  obvious bookkeeping.

**Precise missing lemma (the exact obstruction):**
> Attractor Lemma (all n, both maps): ∀π ∈ S_n ∃k ≤ f(n): s_T^k(π) ∈ {id_n, rev_n}.
>
> A proof seems to need: (i) a well-founded measure Φ on S_n (likely lexicographic/
> structural, since no natural scalar works) that strictly decreases off {id,rev}; or
> (ii) an induction showing each s_T-application settles ≥1 element permanently, with
> uniform accounting when the maximum/minimum is popped mid-run (which does happen:
> s_A(231)=312 pops the 3). Residual quantifiers: ∀n ≥ 1, ∀π ∈ S_n, ∃k — none of the
> three can be cut: n=11 is open computationally here (10! full sweep done; 11! ≈ 4.0·10⁷
> was not run), and both maps need separate treatment (they are not r-conjugate; only
> c-conjugate, and c(T1) = T1^r ∉ {T1,T2}).

## 4. Evidence levels (disposition.json carries the machine-readable form)

- source: primary-body read (arXiv v2 full HTML, retained + refetched byte-identical).
- scope: full exact-scope match to Conjecture 5.1 as stated (both maps, all n, Def 4.1
  periodicity); MathDB record statement (frozen reserved-records.json) is equivalent.
- prior: real bounded pass incl. the 2024 restatement; no live MathDB request (429 hold);
  no Google/GitHub-API/ScienceDirect.
- computation: independent implementation, 17 semantic checks vs 5 proved source theorems,
  recurrence cross-validation, full n ≤ 10 sweeps both maps, all under helper_guard
  (≤ 512 MiB, ≤ 210 CPU s, ≤ 230 wall s per run).

## 5. Next necessary action (root-facing)

Park 347483 with: (a) the n ≤ 10 two-map certification as finite evidence (not a proof);
(b) Theorem E reduction — any future attempt should target the Attractor Lemma directly,
preferably for map B first (hitting bound exactly n−1 hints at a clean induction; the
π₁ = n case is already proved by hand above and generalizes the way Zhang's valley-block
argument works for s_{123,132}); (c) prior-art recheck triggers: any new paper citing
arXiv:2405.01854 Conjecture 4.2, or any MathDB status change on 347483. No acceptance, no
counts change (9 additional / 39 total unchanged; next 40).
