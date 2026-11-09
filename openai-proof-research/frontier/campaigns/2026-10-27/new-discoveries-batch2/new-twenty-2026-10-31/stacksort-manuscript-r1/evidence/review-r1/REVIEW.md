# Independent adversarial review: MathDB 345545 (stack-sorting degree), lane stacksort-review-r1

Reviewer: Claude Opus 5.5 (high effort), working alone with no child agents. This is a review, not an acceptance. Root decides.

Candidate under review: `expanded-corpus-r133/candidate-345545/` (CANDIDATE.md, certificate.json, lean/StackSortDegree.lean). It claims a refutation of Defant and Propp's Conjecture 4.4 (arXiv:2002.07144v3/v4; Conjecture 23 in the EJC version).

## 0. Run history and discipline

- **First run.** It started at 2026-11-03T15:50Z and stopped at about 16:07:53Z on a server-side HTTP 500 (see `launch.json`, `failed_utc`). The stop was not caused by any finding.
- **Resumed run (this one).** It started 2026-11-03T16:08Z.
  - It kept `hashes/inputs-before.sha256`, written by the first run at 15:51Z. At resumption all 165 of those inputs were re-verified OK.
  - It recorded the interruption in `dl-r1/receipts.jsonl` (the `interruption_and_resumption` event line).
  - It inspected every script and log of the first run.
- **What the first run left.**
  - Every log is complete (exit 0), with one deliberate exception: `logs/label_insertion_24.log` hit the 140 s wall cap (exit 124) after printing n = 1..22. That was by design, and the 22 values it printed are the ones used.
- **What this run re-checked.**
  - It re-ran `scripts/topmax.py 82 naive` as a determinism check. The output JSON is byte-identical (sha256 e8f88d0e…715e8a before and after; `logs/topmax_naive_82_rerun.*`).
  - It re-checked both certificates and the table equality with new code (`scripts/seedexact.py`).
- **Lane restrictions.**
  - No Lean, lake, leanchecker, SAT or ILP solver was run.
  - Every computation was a single capped `python3 -I` process (`scripts/run.sh`): taskset to 2 CPUs, an address-space cap of 1.5 GiB, CPU 120 s, wall 140 s, `MALLOC_ARENA_MAX=2`, run one at a time. The largest peak RSS was 331 MB (the label-insertion run). No background job remains.
  - No git, no edits to shared files, no publication, no contact with anyone.
  - Downloads went into fresh directories under `dl-r1/`.
  - None of the discovery lane's scripts was imported or executed.
- **Hashes.** Inputs were hashed before (`hashes/inputs-before.sha256`, 165 files) and after (`hashes/inputs-after.sha256`); the two lists are identical. One extra read-only input, `expanded-corpus-r133/raw/345545.jsonl` (the MathDB record), is not in the before-list. Its hash is recorded separately in `hashes/extra-read-inputs.sha256`: sha256 4ed483b9…d0e2, which equals the `raw_sha256` stored in r133 `results.json`.

## Gate A: statement fidelity. Verdict: QUALIFIED_PASS

### A1. Source text, by version

The four arXiv PDFs were read. v1 to v3 were fetched by this lane (`dl-r1/arxiv-pdf-2002.07144v{1,2,3}`). v4 was fetched again by this lane (`dl-r1/arxiv-pdf-2002.07144v4`), and its sha256 4f9f0708…a12fa matches the discovery lane's copy byte for byte. The open journal PDF, EJC 27(3) (2020) #P3.51 (published 2020-09-04), was also read (`dl-r1/ejc-pdf`).

**Definition 1.1** (v4 text lines 47–55; EJC "Definition 1", line 63; identical in v1 to v4):
- deg(f) = (1/|X|) Σ_{x∈X} |f⁻¹(f(x))|.
- This equals (1/|X|) Σ_y |f⁻¹(y)|², which is the average multiplicity. It is not the maximum fibre.

**Stack-sorting map** (v4 lines 358–366):
- s(∅) = ∅, and s(LmR) = s(L)s(R)m, where m is the largest entry.
- Example: s(416352) = 143256.
- The lane's convention matches. The reviewer's brute force uses both the recursive definition and the one-pass stack; they agree for n ≤ 8 (`scripts/brute.py`, `logs/brute.log`).

**Theorem 2.5** (v4 lines 378–381; EJC "Theorem 8", lines 397–399; same statement in v1 to v4): the limit lim deg(s : S_n → S_n)^{1/n} exists and lies in [1.12462, 4].

**Proof of Theorem 2.5** (v4 lines 385–433):
- n!·d_n counts the pairs (π, π′) with s(π) = s(π′).
- An injection (π, π′, σ, σ′, A) ↦ (π̃(m+n−1)σ̃, π̃′(m+n−1)σ̃′) gives ((m−1)!d_{m−1})((n−1)!d_{n−1})·C(m+n−2, m−1) ≤ (m+n−1)!·d_{m+n−1}.
- Rearranged, this is **inequality (1)**: d_{m−1}d_{n−1} ≤ (m+n−1)·d_{m+n−1} (v4 line 412; EJC line 436).
- **Sup formula:** let a_n = d_{n−1}/n² for n ≥ 8 and a_n = 0 for 1 ≤ n ≤ 7. Then de Bruijn–Erdős gives lim d_n^{1/n} = sup_{n≥1} a_n^{1/n} (v4 lines 413–433). The paper uses the computer value a_10 ≥ 1.12462.
- Small source wrinkle: the lemma is quoted for positive sequences, but a_n = 0 for n ≤ 7. This does not affect anything used here. The lower bound lim ≥ a_n^{1/n} for any n ≥ 8 needs only a_n² ≤ a_{2n}, which holds because 4(2n−1) ≤ n² for n ≥ 8, and the limit, which Theorem 2.5 itself asserts.

**Conjecture 4.4** (v4 line 1027; v3 line 958; EJC "Conjecture 23", lines 1072–1074): "The value of the limit lim_{n→∞} deg(s : S_n → S_n)^{1/n} lies in the interval (1.68, 1.73)."
- Evidence (v4 lines 1020–1026): the mean of |s⁻¹(s(π))|^{1/n} over random π. For 1000 random permutations at n = 100 it was 1.69 (sd 0.09); for 100 at n = 300 it was 1.70 (sd 0.06).
- Problem 4.3 (v4 line 1017) asks to improve the estimates.

**Version finding (not in CANDIDATE.md):**
- **v1 (2020-02-17) and v2 (2020-02-18) contain no Conjecture 4.4.** At the same place (v1 and v2 text line 985) they say only: "This suggests that lim deg_n(s)^{1/n} should lie in the interval (1.6, 1.8)."
- The numbered conjecture with (1.68, 1.73) first appears in **v3 (2020-03-29)**, which is the EJC submission date of 2020-03-27. It is kept in v4 and in the journal.
- The MathDB note "no resolution … (as of February 2020)" therefore dates the conjecture slightly too early. This is harmless.
- The exact table also refutes the weaker v1/v2 remark (1.6, 1.8). The lane's doubling bound exceeds 1.8 for every a from 79 to 82; at a = 82 it is 1.80468. This is checked exactly with integers in `logs/seedexact.log`, at threshold 9/5.

### A2. The MathDB paraphrase

The MathDB record (`raw/345545.jsonl`) says: "let deg(s : S_n → S_n) denote its **maximum fiber size**". The rest of the record copies Conjecture 4.4 and its evidence.

- **Which reading is the conjecture's?** The source reading, the average multiplicity of Definition 1.1, unambiguously. The paraphrase is a transcription defect.
- **Under the maximum-fibre reading the conjecture is trivially false.**
  - The maximum fibre is |s⁻¹(id)| = C_n. The source itself cites |s⁻¹(π)| ≤ C_n (v4 lines 434–440, Bóna, Exercise 23), and s⁻¹(id) = Av(231) has C_n elements.
  - So the limit exists and equals 4.
  - The reviewer's brute force confirms max fibre = |s⁻¹(id)| = C_n for n ≤ 10 (`logs/brute.log`).
- **Simplest rigorous proof (no Catalan theory needed).**
  - Let F_1 = {1} and F_n = {nπ′ : π′ ∈ F_{n−1}} ∪ {π′n : π′ ∈ F_{n−1}}.
  - By the definition of s, s(nπ′) = s(π′)n = s(π′n). So by induction every element of F_n sorts to id_n.
  - The two halves are disjoint, since n is first in one and last in the other, so |F_n| = 2^{n−1}.
  - Hence maxfib_n ≥ 2^{n−1}, and maxfib_n^{1/n} ≥ 2^{(n−1)/n} ≥ 2^{4/5} = 1.7411 > 1.73 for every n ≥ 5. Any limit is therefore at least 2.
  - The family was brute-force checked for n ≤ 10 (`fam True` in `logs/brute.log`).
- **Does the candidate refute both readings?** Yes. The source reading is refuted by the certificate, and the maximum-fibre reading by the family above (CANDIDATE.md line 14 says the same). Credit cannot rest on the maximum-fibre reading.

### A3. The Lean Prop under each reading

Write d_n = (Σ_{σ∈S_n} |{τ : s τ = s σ}|)/n!, which is Definition 1.1 literally, and m_n = max_y |s⁻¹(y)|.

- **Source reading.** The conjecture is `Conj := ∃ L : ℝ, Tendsto (fun n => d n ^ (1/(n:ℝ))) atTop (𝓝 L) ∧ 1.68 < L ∧ L < 1.73`. The candidate's endpoint is `¬ Conj` (Lean draft lines 129–131; CANDIDATE.md line 83).
  - Is `¬ Conj` the right literal negation? Yes, given that the source's own Theorem 2.5 asserts the limit exists.
  - The flaw: `¬ Conj` is also true **vacuously** if the limit fails to exist. So on its own, without existence, it is formally weaker than "the limit exists and lies outside the interval".
  - The candidate's argument never needs existence. It gives an infinite subsequence on which d_n^{1/n} > 1.73.
  - **Required phrasing:** prove `¬ Conj` **together with** a non-vacuity companion. The companion should be `∃ᶠ n in atTop, (1.73:ℝ) < d n ^ (1/(n:ℝ))`, or better the explicit form `∀ k, (1.73:ℝ)^(a_k) < d (a_k)` with a_k = 51·2^k − 1.
  - The companion alone already implies `¬ Conj`. It also implies `limsup ≥ 1.73`, so it is never weaker than the source statement. Optionally, formalise existence (Theorem 2.5, via a de Bruijn–Erdős lemma) and state "the limit exists and is > 1.733"; that is stronger but more expensive.
- **Maximum-fibre reading.** `Conj_max` is the same Prop with m_n in place of d_n. The endpoint is `¬ Conj_max` together with `∀ n ≥ 5, 1.73 < m n ^ (1/(n:ℝ))`.

### A4. No source-internal conflict

- **Against the source's theorems.** The refutation gives lim ≥ 1.73308 (from a = 50), and ≥ 1.80468 using a = 82. The heuristic limit is about 1.95. All of this lies inside [1.12462, 4] (Theorem 2.5) and above Defant's 1.62924 (Troupes, Theorem 7.29).
- **Against the source's evidence.** The evidence is E_π[X^{1/n}] with X = |s⁻¹(s(π))|. By Jensen, E[X^{1/n}] ≤ (E X)^{1/n} = d_n^{1/n}, so the experiment estimates a lower quantity. The data never supported the upper end 1.73. There is no conflict, only a mis-extrapolation.
- **A check with the source's own number.** The computer value a_10 = (d_9/100)^{1/10} with P_9 = 117448188 gives 1.1247 ≥ 1.12462, which is consistent.

**Why QUALIFIED rather than PASS:**
- The endpoint must carry the non-vacuity companion.
- The MathDB statement is literally the maximum-fibre version. If root insists on "the exact MathDB statement", both endpoints should be formalised (the second is cheap), while credit rests on the source reading.
- The version history of the conjecture (v3 onwards) should be corrected in the dossier.

## Gate B: independent mathematics. Verdict: PASS

### B1. Proof steps re-derived (CANDIDATE.md lines 24–67)

1. **Decreasing tree and postorder** (lines 40). σ = LnR corresponds to the tree with root n, left subtree T(L) and right subtree T(R). The in-order reading is σ, and s(σ) = s(L)s(R)n is the postorder reading. The proof is by induction, and it is correct.
2. **P_n = Σ_{(B,B′)} e(Q_{B,B′})** (lines 42–44).
   - σ ↦ (shape B, the labelling w of postorder positions, with w = s(σ)) is a bijection onto (shape, labelling decreasing toward the root).
   - So s(σ) = s(τ) exactly when both shapes carry the same w.
   - The count over w is the number of linear extensions of the union order. Correct.
3. **Closure lemma** (line 46).
   - Descendant sets are postorder intervals [j − a_j + 1, j].
   - The closure D(j) grows by unions of intervals, each of which contains a point already present and ends at most at j. So it stays an interval [m_j, j].
   - Laminarity: if i ∈ D(j) then D(i) ⊆ D(j) by closure. If i < m_j then D(i) ⊆ [1, i], which is disjoint from D(j).
   - i <_Q j exactly when i ∈ D(j)∖{j}, because D(j) is the downward-reachable set.
   - The elements above any i form a chain, so Q is a forest poset. Correct.
4. **Forest hook-length formula** (line 48–49). e(Q) = n!/Π|D(j)| is standard (Knuth, TAOCP 3, §5.1.4, Ex. 20). Applied correctly. *It is not needed for an integer (labelled) computation; see Gate C.*
5. **Block recursion** (lines 52–65).
   - **Common cut points.** A common cut point c starts a tree in both forests, so no tree and no descendant interval crosses c. Hence every D(j) stays on one side, and the weight factorises. This gives the bijection with sequences of irreducible pairs. Correct.
   - **h_m = m in an irreducible pair.** The lane's argument is correct: if D(m) = [c, m] with c > 1, the F-tree containing c−1 cannot end at or after c, because its root would lie in D(m). So c is an F-cut, and likewise an F′-cut.
   - *A simpler argument found here:* the label m is the maximum, so it is a root in both forests and sits at the right end of a tree in both. If its position p were less than m, then p+1 would be a common cut point. So w(m) = m, without the closure lemma.
   - **Root deletion.** The root has t children with multiplicities μ = (1, 2, 1) and R = r−1+t. All D(j) with j < m are unchanged. Correct.
   - **Cut points of the original pair.** They are the starts of reduced trees 2..min(r, R), plus position m when t = 0. Checked separately for t = 0 (R = r−1) and t ≥ 1 (R ≥ r). Correct.
   - **Irreducibility criterion.** The original pair is irreducible iff (t, u) ≠ (0, 0) and no reduced block boundary has cumulative counts (ρ, ς) with ρ < min(r, R) and ς < min(s, S). Both counts increase from left to right, so it is enough to test the first boundary. This is exactly the condition "r₁ ≥ min(r, R) or s₁ ≥ min(s, S)" that defines Y. Correct.
   - **Base cases and integer form.** I(1,1,1) = 1 and d_n = I(1,1,n). The integer form uses multinomial (binomial) shuffles. Correct.
6. **Doubling lemma** (lines 30–36).
   - Inequality (1) with m = n = a+1 gives d_a² ≤ (2a+1)d_{2a+1}, or in integers C(2a, a)·P_a² ≤ P_{2a+1}.
   - With a_{k+1} = 2a_k + 1 and A_k = a_k + 1 = 2^k(a+1), we get u_{k+1} ≥ u_k − log(a_{k+1})/(a_{k+1}+1).
   - The step log(a_{k+1}) ≤ log(a_{k+1}+1) is a valid weakening.
   - The series sum is right: Σ_{j≥1}(j log 2 + log(a+1))/(2^j(a+1)) = (2 log 2 + log(a+1))/(a+1) = log(4(a+1))/(a+1), because Σ j/2^j = 2 and Σ 1/2^j = 1.
   - Since d_n ≥ 1, u_k ≥ 0, and d_{a_k}^{1/a_k} ≥ e^{u_k} ≥ (d_a/(4(a+1)))^{1/(a+1)} **for every k**. Existence of the limit is not needed. Correct.
   - **Simpler equivalent found here (useful for Lean).** With c = d_a/(4(a+1)), induction gives **d_{a_k} ≥ 4A_k·c^{2^k}**. The base case is an equality. The step is d_{a_{k+1}} ≥ d_{a_k}²/a_{k+1} ≥ 16A_k²c^{2^{k+1}}/(2A_k − 1) ≥ 8A_k c^{2^{k+1}} = 4A_{k+1}c^{2^{k+1}}. If c > 1.73^{a+1}, then d_{a_k} > 1.73^{A_k} > 1.73^{a_k} for all k. This needs no logarithms and no series.

### B2. Independent computation

Three algorithms were used. Each was written from the mathematics; none is a transcription of the lane's Y-criterion block recursion.

- **Brute force** (`scripts/brute.py`): P_n for n ≤ 10 over all of S_n, using the literal recursive s (cross-checked against the one-pass stack for n ≤ 8).
- **Label insertion** (`scripts/label_insertion.py`), a different state space.
  - It builds both decreasing forests together by inserting the labels 1, 2, …, n in increasing order.
  - Each new label is a common root over 0, 1 or 2 consecutive roots (weights 1, 2, 1), placed at a gap that is a tree boundary in both forests.
  - The state is the word of boundary flags in {1, 2, 3}. It uses no hook formula, no blocks and no tree-count index. It gave n ≤ 22 within the cap.
- **Top-max subtraction recursion** (`scripts/topmax.py`), a different decomposition.
  - It counts labelled forest pairs XI[M][r][s] and irreducible pairs II[M][r][s].
  - It uses the *last* block (not the first) and the identity "label M at position M" counted two ways: by deleting the common last root, and by conditioning on the last irreducible block.
  - From that it gets II[M] by subtraction. It uses no hook-length formula, no closure lemma and no Y criterion.
  - It shares the (M, r, s) indexing with the lane, so it is independent in decomposition, not in the index set.
  - It reached n = 82 in naive mode (25 s, 18 MB) and in Kronecker-packed mode (25 s, 37 MB); the two agree.
- **Results** (`logs/certify.log`, `logs/seedexact.log`):
  - brute = label insertion = top-max for n ≤ 10;
  - label insertion = top-max for n ≤ 22;
  - top-max naive = packed for n ≤ 82;
  - **the lane's `outputs/stack_pairs_P_1_82.json` equals the reviewer's table exactly for n = 1..82, with no mismatches.**
- **Small values:** P_1..P_20 = 1, 4, 26, 224, 2356, 29064, 411172, 6573624, 117448188, 2322885008, 50429847572, 1192782788192, 30533141865700, 841025569061736, 24802500974885020, 779708932637648392, 26028895710444355516, 919586611535156918680, 34279121480711537327388, 1344580237342589147760320.
- **Certificate value:** P_50 = 9385583269767512161193412991288095407166959926264841564653575816719248830768416.
- **Full table:** `outputs/reviewer_P_1_82_and_certificates.json` (sha256 06c2da70…b15a).

### B3. Certificates (exact integers, checked twice: `logs/certify.log` and `logs/seedexact.log`)

- P_50·100^51 > 4·51·50!·173^51: **true**. The doubling bound is 1.7330806.
- P_78·100^79 > 79²·78!·173^79: **true**. The source sup-formula bound (d_78/79²)^{1/79} is 1.7319022.
- **Smallest a for which the doubling bound exceeds 1.73: a = 50.** At a = 49 it is 1.72959. It holds for every a from 50 to 82.
- **Smallest n for which the source sup formula alone exceeds 1.73: n = 79 (using d_78).** At n = 78 it is 1.72979.
- At threshold 1.8, the doubling bound first exceeds it at a = 79; the sup formula does not exceed it for any n ≤ 83.
- Heuristic (not proof): d_82^{1/82} = 1.95107 and d_82/d_81 = 1.95411. This is consistent with the lane's extrapolated limit of about 1.953.

## Gate C: Lean route design (no Lean run). Verdict: QUALIFIED_PASS

A cheap, kernel-checkable route exists. The lane's draft is a reasonable skeleton but not a proof plan to execute as written.

### C1. Recommended route (source reading)

- **L1, literal s and deg.**
  - Define s on `List ℕ` by the max split, and give it on `Perm (Fin n)` via one-line notation.
  - Prove that sList σ is the one-line form of a permutation (a bridge to a literal s : S_n → S_n), or argue that Definition 1.1 depends only on the fibres.
  - Prove deg n = P n / n! with P n = #{(σ, τ) : s σ = s τ}, by `Finset.sum_comm` or card of a sigma type.
- **L2, standardisation (order-equivariance).** For an order-preserving relabelling φ of values, s(φ∘w) = φ∘s(w); also s(L m R) = s(L)s(R)m. Every later lemma needs this. It is the main source of formalisation friction.
- **L3, the doubling injection.** C(2a, a)·P_a² ≤ P_{2a+1} (the source injection with m = n = a+1).
- **L4, the iteration invariant.** d_{a_k} ≥ 4A_k·c^{2^k} (B1.6). Proof by induction on k in ℝ, using only L3. No logarithms or series.
- **L5, wrap-up.**
  - From c > 1.73^{51} (certificate) derive ∀ k, 1.73^{a_k} < d_{a_k}, so `∃ᶠ n in atTop, 1.73 < d n ^ (1/n)`.
  - Then `¬ Conj` follows by `ge_of_tendsto` along the strictly monotone a_k.
  - This needs only rpow monotonicity and `Tendsto.comp` with `StrictMono.tendsto_atTop`.
- **L6, lower bound P_a ≥ G_a at a feasible a.** Recommended split (route C2):
  - **(i) Elementary root-split inequality**, for n ≥ 2: P_n ≥ 4P_{n−1} + Σ_{i=1}^{n−2} C(n−1, i)·P_i·P_{n−1−i}.
    - The proof is an injection from the disjoint union of (a) pairs (LnR, L′nR′) with |L| = |L′| = i, s(L) = s(L′) and s(R) = s(R′), counted as C(n−1, i)·P_i·P_{n−1−i} including i = 0 and i = n−1, and (b) the cross pairs (nR, L′n) and (Ln, nR′), giving 2P_{n−1}.
    - It needs only L2 and the definition. It was checked to hold for n = 2..82 against the exact table (`logs/certify.log`).
  - **(ii) Exact seeds P_1..P_16**, or P_1..P_20, from a proved exact recursion evaluated in the kernel.
  - **(iii) Kernel evaluation** of the monotone recursion G (with G ≤ P by induction from (i)) up to a = 230, or a = 130, followed by the integer test at that a.
  - **Exact first a** at which the doubling test passes, by seeds: ≤ 20 gives a = 130; ≤ 16 gives a = 230; ≤ 14 gives a = 446; ≤ 13 gives a = 910 (`logs/seedexact.log`). Seeds ≤ 12 do not reach 1.73 for a ≤ 3000, since the asymptotic ratio of G is 1.73008 (`logs/seedscan.log`).
- **L7, an exact recursion for the seeds. Recommendation: top-max on tuples of words, not trees.**
  - XI[M][r][s] counts pairs of ordered set partitions of [M] into r and s nonempty words with s(σ_1)⋯s(σ_r) = s(τ_1)⋯s(τ_s).
  - Lemmas needed:
    - (T1) Common-cut factorisation with a binomial shuffle, using L2.
    - (T2) In an irreducible pair the common output ends with M. Proof in two lines: M ends its own block in both tuples, so a smaller position would be a common cut.
    - (T3) Deleting M from σ_r = A M B: s(σ_r) = s(A)s(B)M. Multiplicities 1, 2, 1 for the number of nonempty parts among A and B.
    - (T4) The two expressions for KI, as additive identities in ℕ to avoid truncated subtraction.
  - **Not needed:** decreasing trees, the closure lemma, the forest hook-length formula, and the Y irreducibility criterion.
  - The lane's own labelled block recursion is also usable. It needs T1, T2, T3 and the "if" direction plus uniqueness of the Y criterion, but the top-max form has fewer lemmas.
- **Restricted-family question.** No simpler self-contained family suffices. The elementary recursion alone, with seeds that the kernel could brute-force (n ≤ 8), plateaus at about 1.63 (`logs/seedscan.log`: seeds ≤ 8, best 1.632). So some exact recursion (L7) has to be proved. Seeds ≤ 13 or 14 are within brute-force range on paper, but not in the kernel.

### C2. Kernel cost estimates

These are counts of big-integer multiplications, from `logs/opcount.log` and `logs/seedexact.log`.

| Piece | Multiplications | Notes |
|---|---|---|
| Top-max exact table to N = 16 | 17,970 | |
| Top-max exact table to N = 20 | 51,641 | |
| Top-max exact table to N = 50 | 7,360,940 | the direct P_50 route |
| Top-max exact table to N = 78 | 98,331,974 | the sup route |
| Elementary recursion 16 → 230 | 52,216 | numbers up to about 1.6k bits |
| Elementary recursion 20 → 130 | 16,280 | |
| Elementary recursion 14 → 446 | 197,856 | |
| Elementary recursion 13 → 910 | 826,137 | numbers up to about 8.4k bits |
| Certificate test at a | about a | powers and a factorial |

- **Recommended:** seeds to N = 20 plus elementary recursion 20 → 130, about 68k operations; or N = 16 plus 16 → 230, about 70k.
- The direct P_50 route (7.4M) and the P_78 sup route (98M) are likely too heavy for `decide` without `native_decide`.
- Lean 4's kernel has GMP-accelerated `Nat` literal arithmetic. The real cost is reduction overhead, so tables must be built bottom-up as a structural fold with sharing, or supplied as literal data and checked row by row. A naively recursive definition re-evaluates subproblems exponentially in the kernel, and well-founded recursion does not reduce reliably.

### C3. Maximum-fibre add-on

Cheap. It needs: the definition of maxfib, the two-line identity s(nπ′) = s(π′)n = s(π′n), injectivity of the family, card 2^{n−1}, then rpow. Probably under 300 lines on top of L1 and L2.

### C4. The lane's uncompiled draft (`lean/StackSortDegree.lean`)

**Right:**
- `stackSort` (lines 19–26) is the literal max-split definition. `foldr max 0` is the maximum for nonempty ℕ-lists.
- `deg` (lines 41–44) is literally Definition 1.1 for the fibres of `sList`.
- `doubling_comb` (line 60) is the correct integer form of (1).
- `limit_ge_of_doubling` (lines 67–70) is a true statement.
- `cert_ineq` (line 121) is true; `decide` or `norm_num` should handle it.
- The endpoint (lines 129–131) is the literal negation of the existential form.
- The `DPTable.Valid` equations (lines 89–105) transcribe `stack_pairs_int.py` correctly and determine a unique table. (The hypothesis `r ≤ m + 2` is looser than needed, but it is consistent, since both sides are 0 there.)

**Wrong or weak:**
- (a) The endpoint has no non-vacuity companion (see A3).
- (b) The `decreasing_by … sorry` on line 30 must be discharged. It needs m ∈ l, which the `let` binding hides. Use `have` or define s by fuel.
- (c) `sList` lands in `List ℕ`, not S_n. That is acceptable for Definition 1.1, but there is no bridge lemma; values run 0..n−1, which is harmless.
- (d) `dp_50` (line 115) evaluates an *abstract* `T`, which cannot be kernel-reduced. A concrete, shared, bottom-up table function is needed, and at n = 50 it is about 7.4M operations.
- (e) `P_eq_dp` (line 109) is one sorry that holds the entire combinatorial content, and its comment still cites the hook-length formula, which is unnecessary.
- (f) `limit_ge_of_doubling` plans a log or series proof; the invariant in B1.6 is shorter.
- (g) `deg_eq`, `P_pos`, `doubling`, `exists_table` and `hcert` are all `sorry`.

**Estimate:** medium. The pieces are L2 (standardisation) and L7 (T1 to T4), then kernel evaluation of about 70k operations. This is lighter than the lane's own "medium-high" estimate because the hook formula, the closure lemma and the series are all avoidable.

## Gate D: prior art (bounded). Verdict: PASS (bounded search; no prior refutation, computation or growth-constant estimate found)

All fetches are logged with URL, UTC time, status, size and sha256 in `dl-r1/receipts.jsonl`.

- **OpenAlex.**
  - The source is W3006538269 (DOI 10.37236/9475).
  - **Cited-by** (`filter=cites:W3006538269`): 5 works. All were read or screened:
    1. Defant, *Troupes, Cumulants, and Stack-Sorting* (arXiv 2004.11367v2, Adv. Math. 2022), body read from the r133 hash-bound copy.
       - The intro (lines 186–197) and §7.6 (lines 3096–3180) restate the (1.68, 1.73) conjecture as open.
       - **Theorem 7.29**: lim > 1.62924, via −c_1000 and the source sup formula.
       - **Remark 7.30**: brute force cannot exceed about n = 14.
       - *Campaign lesson:* its stated numbers do not contradict the conjecture, since 1.62924 < 1.68.
    2. Bouvel, Cioni and Ferrari, *Preimages under the Bubblesort Operator* (arXiv 2204.12936, EJC 2022). Body fetched: it is about bubblesort, does not even cite the paper in its arXiv reference list, and has nothing on s or deg.
    3. Defant, *Fertilitopes* (arXiv 2102.11836, DCG 2023). Body fetched: it cites the paper only as "combinatorial dynamics [17, 27]" (line 52) and has no degree estimates.
    4. Fried, *The minimal sum of squares over partitions with a nonnegative rank* (arXiv 2204.07873, r133 copy). About general maps, with no stack-sorting at all (0 occurrences of "stack").
    5. Madhumitha and Naduvath, *Graphs defined on rings: a review* (Mathematics 2023). Screened by title and venue as off-topic; body not fetched (MDPI).
  - **Search "degree of noninvertibility"**: 7 hits. Besides the works above, Fried, *The expected degree of noninvertibility of compositions of functions…* (arXiv 2202.13061): body fetched, random maps only, no "stack".
  - **Search "stack-sorting degree of noninvertibility"**: 153 hits. Screened the top 25; the only relevant ones are the source, Troupes and Fertilitopes.
  - **Works citing Troupes** (`filter=cites:W3018498331`): 22 works, all screened by title. Those plausibly relevant were read:
    - Defant and Lee, *Boolean, free, and classical cumulants as tree enumerations* (arXiv 2409.05219, AAM 2025): no "noninvertib", 1.62924, 1.68 or 1.73.
    - Defant, *Stack-sorting for Coxeter groups* (arXiv 2104.03215): no hits.
    - The r133 copies of Defant 2003.05935v2 and Zhang 2606.24110 (*Asymptotics of the average stack-sorting depth*, 2026): no hits for deg or noninvertibility.
- **OEIS.**
  - The JSON queries `1,4,26,224,2356,29064,411172,6573624` and `2356,29064,411172` returned `null`.
  - The text-format queries `1,4,26,224,2356`, `4,26,224,2356,29064,411172` and `2322885008` (P_10) each returned "No results".
  - So the sum of squared fibre sizes of s is not in the OEIS.
- **arXiv.** The abs page lists v1 to v4 (latest 2020-09-27) with no withdrawal or comment. The journal page (combinatorics.org, P3.51, published 2020-09-04) shows no erratum. The arXiv author listing `arxiv.org/a/defant_c_1` returned 404 (recorded, not retried).
- **Not used, by instruction:** Crossref, Semantic Scholar, the arXiv search API and ScienceDirect.
- **Limits.** This is a bounded search: OpenAlex coverage, a sample of bodies, and OEIS. Google Scholar, MathSciNet and zbMATH were not consulted.
- **Correction or withdrawal of Conjecture 4.4:** none found. **Any computation of the growth constant beyond 1.62924:** none found.

## Gate E: significance and exclusion screen. Verdict: QUALIFIED_PASS

- **Known result?** No. No prior bound above 1.62924 and no table of P_n was found (Gate D).
- **Routine consequence of a published theorem?** No. The source's theorems give only [1.12462, 4], and Troupes gives > 1.62924. Refuting the conjecture needs new exact data: P_n for n ≥ 13 has never been published (the source computed only a_10).
- **Adversarial finding: the refutation is shallower than CANDIDATE.md line 76 claims.**
  - Line 76 says "the new polynomial formula is the key". The exact table needs a new algorithm for n ≥ 15 or so.
  - But the refutation **itself** follows from exact P_1..P_13 plus the elementary root-split inequality and the source's (1): the doubling test passes at a = 910 (exact integers, `logs/seedexact.log`).
  - P_13 (13! ≈ 6.2·10⁹) is within the brute-force range Defant cites in Remark 7.30.
  - So the conjecture was refutable with brute force and a five-line inequality. This lowers the depth, not the validity.
  - The polynomial-time formula, the exact P_n to 82, the proven bound ≥ 1.8047, and the estimate of about 1.95 are genuine additions beyond the bare refutation.
- **Wording artefact?** No. Credit rests on the source reading (Definition 1.1); the maximum-fibre MathDB paraphrase is not used for credit (A2).
- **Source-internal conflict?** None (A4).
- **Degenerate example?** No. It refutes a numerical conjecture about a well-studied map, published in EJC and restated as open in Adv. Math. 2022, and by a wide margin: the proven bound is ≥ 1.8047 and the heuristic limit is about 1.95.
- **Recommendation.** Count it as a genuine refutation of a published conjecture, with **moderate** significance. Root should note the brute-force-seed observation when it assesses significance against the campaign's "routine" bar.

## Overall recommendation: PROCEED (to Lean formalisation), with conditions

1. **Endpoint.** Formalise `¬ Conj` (source reading, Definition 1.1 literally) **plus** the non-vacuity companion `∀ k, 1.73^{a_k} < d (a_k)` (or `∃ᶠ`). Also add the cheap maximum-fibre endpoint `¬ Conj_max` so that the literal MathDB wording is covered. Credit rests on the source reading only.
2. **Route.** Use L1 to L7 (top-max recursion on tuples of words; seeds to N = 20 or 16; elementary recursion to a = 130 or 230; the iteration invariant from B1.6). Avoid the hook-length formula, the closure lemma, the series and the 7.4M-operation P_50 evaluation.
3. **Dossier corrections for CANDIDATE.md.**
   - Conjecture 4.4 exists only in v3, v4 and the EJC version (as Conjecture 23); v1 and v2 have only the "(1.6, 1.8)" remark, which is also refuted (≥ 1.8047).
   - Temper the line 76 claim, since brute-force seeds to 13 suffice.
   - Record the simpler h_m = m argument and the series-free invariant.
4. Independent fidelity review of the eventual Lean statement, and the clean extracted replay, as required by the campaign.

Not self-accepted. Credit is zero until root accepts.

## Files in this lane

- **Scripts:** `scripts/` (brute.py, label_insertion.py, topmax.py, certify.py, elementary.py, opcount.py from the first run; seedscan.py and seedexact.py from the resumed run; run.sh; fetch.sh).
- **Logs:** `logs/` (each run has a .log including the command, script sha256, exit code, RSS and time; plus .stderr and .time files). The resumed-run logs are seedscan, seedexact and topmax_naive_82_rerun (with pre- and post-hash).
- **Outputs:** `outputs/`. `reviewer_P_1_82_and_certificates.json` is the P table. Also brute_P.json, label_insertion_P.json (written by the n ≤ 14 run; the n ≤ 22 values are in `logs/label_insertion_24.log`), topmax_P{24,50,82}_naive.json, topmax_P82_packed.json, elementary_recursion.json, seedscan.json and seedexact.json.
- **Receipts:** `dl-r1/receipts.jsonl`; each fetch has its own directory with body, headers.txt, receipt.json and text.txt.
- **Hashes:** `hashes/inputs-before.sha256`, `hashes/inputs-after.sha256`, `hashes/extra-read-inputs.sha256`, `hashes/lane-files.sha256`.
