# T008M independent proof review, round 1

Reviewer: independent PROOF reviewer (Claude Opus 5.5). Not author assistance, not a contribution, formal, manuscript or acceptance gate. Original prose CC BY 4.0; original code MIT.

## Verdict

**PASS_FULL_T008M.**

The frozen author proof (candidate-008.md, SHA256 `0bf87bca…5f`) establishes the unchanged full scope (scope-008.md, SHA256 `8ad29468…39`). This is relative to the stipulated pinned source theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I found no mathematical gap and no counterexample. **No required objection.** The optional objections O1–O7 below are exposition items or improvements. None changes the theorem, its quantifiers or the proof's validity.

There is one substantive observation, O1. The three-cap construction and the weight-three padding are valid but unnecessary: the single block Phi_N is already faithful on A_N. This is not a proof defect. It does affect how the "integrated contribution" is described, because source-and-credit.md lists "three adjacent caps and weight-three padding" among the proposed new ingredients. The parent and the separate contribution reviewer should know this. I did not read the contribution packet or brief.

## Exact scope checked (unchanged)

For every field F of characteristic 0, let W_F be the source Ihara Lie algebra W ⊗_Q F, and let g_N = W_F / W_{>N}. The claim is that there are absolute c, C > 0 and N0 such that, for all F and all N ≥ N0,

c ρ^{N/2}/√N ≤ μ_F(g_N) ≤ μ_nil,F(g_N) ≤ C ρ^{N/2}, where ρ^3 = ρ + 1 and ρ > 1.

Both Nth-root limits equal √ρ. The construction must be an explicit finite 0/1 generator-matrix state construction in free homogeneous generators. The scope makes no claim about canonical or efficient conversion, a fixed alphabet or class, an exact minimum, or an improved polynomial factor. Every quantifier is preserved by the candidate:
- all characteristic-0 fields;
- all N ≥ N0;
- unbounded nilpotency class;
- the full infinite alphabet of odd weights at least 3;
- letters that cross the cut, of any weight;
- inhomogeneous elements.

## Independent reconstruction

The reconstruction below is my own derivation. I compared it with the candidate step by step.

**R1. Source interface and scalar extension.** I read thm:main (01-introduction.tex). It gives a graded Lie isomorphism Lie_Q⟨e_3,e_5,…⟩ ≅ (W,{,}) with wt e_d = d, and it states that the generators are noncanonical. Tensoring with F gives Lie_Q⟨e⟩ ⊗ F ≅ W_F. By the universal property, Lie_Q⟨X⟩ ⊗ F is the free F-Lie algebra on X, because Hom_F(L ⊗ F, h) = Hom_Q(L, h) = Map(X, h). So W_F ≅ L_F := Lie_F⟨e⟩ as graded Lie algebras, and (W_F)_{>N} corresponds to L_{F,>N}.

I also read lem:lie-lattice (02-algebra.tex, lines 25–64). It states that the bracket span in the free associative algebra rationalizes to Lie_Q⟨X⟩, including for weighted alphabets with finitely many letters in each bounded weight. Its proof records PBW (U = free associative algebra). Hence L_F ⊂ A_F = F⟨e⟩ is a graded Lie embedding under the commutator bracket. Over a field this is also classical.

Because the embedding is graded, L_F ∩ A_{>N} = L_{F,>N}. Therefore g_N ↪ A_N := A/A_{>N} is an injective Lie homomorphism. A faithful associative representation of A_N restricts to a faithful Lie representation of g_N. ✔

**R2. States, levels and transitions.** P_m = {(a,r): r ≥ 1, wt a + r ≤ m} has level −(wt a + r). Q_b = {(v,s): s ≥ 0, wt v + s ≤ b} has level wt v + s. For each odd d ≥ 3, X_d has 1 at (source row, target column) exactly for these three transitions:
- deletion: P(e_d a, r) → P(a, r);
- crossing: P(∅, r) → Q(∅, d − r), with 0 ≤ d − r ≤ b;
- creation: Q(v, s) → Q(v e_d, s), with wt v + d + s ≤ b.

The target of a deletion is automatically a state.

Level checks:
- deletion: −wt a − r − (−wt a − d − r) = d;
- crossing: (d − r) − (−r) = d;
- creation: d.

The sides are fixed: P→P, P→Q and Q→Q, so there is no Q→P transition. For a fixed d and a fixed source, the target is unique. Deletion needs a nonempty word and crossing needs an empty one; Q states only create. Conversely, the source is unique given the target. Crossing targets have an empty word and creation targets a nonempty word, so the cases never overlap. Hence **every X_d is a 0/1 partial-permutation matrix**. All its nonzero entries go from a state to a state of level exactly d higher. Ordered by level, X_d is strictly upper triangular, and ties never carry entries. Levels lie in [−m, b], so X_d = 0 for d > T = m + b. ✔

**R3. Product orientation.** (X_{d1}⋯X_{dk})_{p,q} = Σ over i_0 = p, …, i_k = q of Π_t (X_{dt})_{i_{t−1}, i_t}. This counts labelled paths that read the word e_{d1}⋯e_{dk} left to right from row p to column q. Each X_d is a partial function on rows, so there is **at most one path**, and every entry of Phi_T(w) is 0 or 1. A nonzero entry has level difference wt w. Hence Phi_T(A_{>T}) = 0, so Phi_T factors through A_T and through A_N for every T ≤ N. ✔ I confirmed this orientation by dense integer matrix products against path following for all words of weight up to cap + 3 and caps 1–11.

**R4. Cut decomposition, including letters of any weight across the cut.** Let w = e_{d1}⋯e_{dk} have weight T ≥ m ≥ 1. Write S_0 = 0 < S_1 < … < S_k = T for the prefix sums. Let i be the least index with S_i ≥ m; it exists because S_k = T ≥ m, and i ≥ 1 because S_0 < m. Then a = e_{d1}⋯e_{d_{i−1}}, d = d_i and v = the rest, with:
- r = m − S_{i−1}, so 1 ≤ r ≤ m;
- s = S_i − m = b − wt v ≥ 0;
- r + s = d_i.

Equality S_i = m gives s = 0, which is allowed. A letter with d_i > m, or d_i spanning the whole cut, is handled identically. No "cut between letters" assumption is used. ✔

**R5. Extraction, uniqueness and multiplicity 1.** Let p = P(a,r) (level −m) and q = Q(v,s) (level b). Take any word u with Phi_T(u)_{p,q} ≠ 0, and follow the unique path:
- While the P-word is nonempty, the only applicable rule is deletion of its first letter, so u must begin with a.
- At P(∅, r), only crossing applies, with letter weight d′ going to Q(∅, d′ − r).
- In Q the gap s never changes, so d′ − r = s, that is d′ = d. Here I use **one generator per odd weight**: weight d′ determines the letter.
- Creation must then build exactly v.

So u = a e_d v = w, and the entry equals 1 by R3. For f = Σ c_u u ∈ A[T], this gives Phi_T(f)_{p_w,q_w} = c_w. So Phi_T is injective on A[T] over **any** field. This is linear coefficient extraction, not semigroup separation. Distinct words have distinct extracting pairs, because (p,q) determines (a, r, v, s) and hence w, though injectivity does not even need this. ✔

My controls confirm that this hypothesis is load-bearing. With two weight-3 letters, the entry for (3,3,3) also equals 1 on (3,3′,3). Flipping the gap sign, prepending instead of appending, or allowing Q→P each fail extraction or the weight cutoff.

**R6. Three caps and padding.** Fix N ≥ 3 and caps T ∈ {N−2, N−1, N}, with m = ⌊T/2⌋ (or m = 1 for T = 1). Residue lemma: for 0 ≤ k ≤ N, if k ≥ N − 2 take T = k; otherwise the three consecutive caps contain T ≡ k (mod 3) with T > k. Then j = (T − k)/3 ≥ 0. Right multiplication by e_3^j sends distinct words to distinct words, so it is injective on A[k] → A[T], and T ≤ N.

For nonzero homogeneous f of weight k: Phi_T(f) Phi_T(e_3)^j = Phi_T(f e_3^j) ≠ 0 by R5, so Phi_T(f) ≠ 0. ✔

**R7. Inhomogeneous faithfulness.** In each block, the homogeneous component f_k is supported on entries with level difference exactly k (R3). Different k use disjoint entry sets. Hence Phi_T(f) = 0 forces Phi_T(f_k) = 0 for every k, in each block. If Φ(f) = 0, then every f_k fails R6, so every f_k = 0. The constant term maps to a scalar multiple of the identity. The argument does **not** assume that homogeneous injectivity implies total injectivity; it proves the reduction by level grading. ✔

**R8. Nilrepresentation and explicitness.** g_N has only positive weights, since W_1 = W_2 = 0 and the generators have weights ≥ 3. Its image is therefore strictly upper triangular in the concatenated level orders. This gives μ_nil,F(g_N) ≤ D := D_N + D_{N−1} + D_{N−2}, and μ ≤ μ_nil trivially.

Each generator σ_d maps to blockdiag(X_d^{(N)}, X_d^{(N−1)}, X_d^{(N−2)}), which has 0/1 entries. The state lists and edges are finite and enumerable, and the same matrices work over every field. ✔ For "any homogeneous free-generator system", see O2.

**R9. Counts and the upper bound.** The generating function is A(z) = 1/(1 − z^3/(1 − z^2)) = (1 − z^2)/(1 − z^2 − z^3). This gives a_0 = 1, a_1 = a_2 = 0 and a_j = a_{j−2} + a_{j−3} for j ≥ 3. By induction, a_j ≤ ρ^j, using ρ^{j−2} + ρ^{j−3} = ρ^{j−3}(ρ + 1) = ρ^j.

The exact counts are:
- |P_m| = Σ_{j<m} (m − j) a_j ≤ ρ^m Σ_{i≥1} i ρ^{−i} = ρ^{m+1}/(ρ − 1)^2;
- |Q_b| = Σ_{j≤b} (b − j + 1) a_j ≤ ρ^b Σ_{i≥0} (i + 1) ρ^{−i} = ρ^{b+2}/(ρ − 1)^2.

With m ≤ T/2 and b ≤ (T + 1)/2, this gives D_T ≤ K ρ^{T/2} with K = (ρ + ρ^{5/2})/(ρ − 1)^2 ≈ 31.72. Then D ≤ K ρ^{N/2}(1 + ρ^{−1/2} + ρ^{−1}) ≤ 3K ρ^{N/2} for N ≥ 4. All constants are independent of F, N, the class and the generator choice. ✔ (Finite check: the maximum of D_T/ρ^{T/2} over 2 ≤ T ≤ 399 is about 5.32 < K.)

**R10. Weighted Witt identity and the lower bound.** PBW gives A(z) = Π (1 − z^n)^{−l_n}, where l_n = dim L_n. This number is field-independent: it is the Lyndon count, and over F it comes from the base change in R1. Hence q_n := n[z^n] log A = Σ_{d|n} d l_d, and Möbius inversion gives n l_n = Σ_{d|n} μ(d) q_{n/d}.

Next, log A = log(1 − z) + log(1 + z) − Σ_θ log(1 − θz), where 1 − z^2 − z^3 = Π (1 − θz) over the roots θ of t^3 − t − 1. This gives q_n = ρ^n + α^n + ᾱ^n − 1 − (−1)^n. The cubic has a single real root: its local maximum, at −1/√3, has value 2/(3√3) − 1 < 0. The product of the roots is 1, so |α| = ρ^{−1/2} < 1 and |q_n − ρ^n| ≤ 4.

The terms with proper divisors have arguments n/d ≤ n/2, and there are at most n of them. So n l_n ≥ ρ^n − 4 − n(ρ^{n/2} + 4).

Explicit threshold (my addition, see O4): n/2·ln ρ − ln(4n) increases for n > 2/ln ρ ≈ 7.1, and it is nonnegative at n = 36. So ρ^{n/2} ≥ 4n for all n ≥ 36. Then n ρ^{n/2} ≤ ρ^n/4 and 4 + 4n ≤ 16n^2/4 ≤ ρ^n/4, so l_n ≥ ρ^n/(2n) for all n ≥ 36.

A faithful representation of dimension M gives an injection g_N ↪ gl_M(F), so M^2 ≥ dim g_N ≥ l_N. Hence μ_F(g_N) ≥ ρ^{N/2}/√(2N), which is the lower bound with c = 1/√2. So the scope holds with c = 1/√2, C = 3K and **N0 = 36**, all absolute. I also checked the Witt inversion exactly against Lyndon enumeration for weights 1–20. (As a finite remark only: for 3 ≤ n ≤ 200 the inequality fails only at n = 4 and n = 6.)

**R11. Limits.** (c ρ^{N/2}/√N)^{1/N} → √ρ and (C ρ^{N/2})^{1/N} → √ρ. By the squeeze, both μ and μ_nil have Nth-root limit √ρ. ✔

## Objections

**Required: none.**

**Optional (non-blocking):**

- **O1. One cap suffices; the three caps and e_3-padding are redundant.** In a single block Phi_T, for every weight 1 ≤ k ≤ T, put m′ = min(m, k) and b′ = k − m′ ≤ b. Then P(a, r) with wt a + r = m′ and Q(v, s) with wt v + s = b′ are states, and R4–R5 apply verbatim with (m′, b′) in place of (m, b). So Phi_T is injective on every A[k] with k ≤ T. With R7 it is faithful on A_T, and Phi_N alone is a faithful nilrepresentation of g_N.

  Consequences: the constant improves to C = K, and the residue lemma and padding become unnecessary. A finite check agrees: single-cap rank equals dim A_N for N ≤ 22 over Q and GF(2), and sub-level extraction holds for 444 words with caps up to 18.

  The author's three-cap proof remains correct. However, "three adjacent caps and weight-three padding" should not be presented as a necessary or new ingredient. This bears on the contribution description and should go to the parent and contribution review. It is not a proof defect.

- **O2. "Any homogeneous free-generator system."** Extraction needs exactly one generator per odd weight. State why this holds for *every* homogeneous free generating set of W_F, not only the source's σ. Such a set maps bijectively onto a homogeneous basis of W_F/[W_F, W_F], and by thm:main that space is one-dimensional in each odd weight ≥ 3 and zero otherwise. One sentence suffices.

- **O3. Residue lemma.** State and prove explicitly the existence of j ≥ 0 with k + 3j ∈ {N−2, N−1, N} (R6). Not needed if O1 is adopted.

- **O4. Explicit N0.** "Sufficiently large" is valid for existence, but N0 = 36 (with c = 1/√2 and C = 3K, or C = K under O1) can be stated with the two-line argument in R10.

- **O5. Scalar extension and source wording.** Add the one-line universal-property argument L_Q ⊗ F = L_F (R1). Also note that lem:lie-lattice's *statement* gives the bracket-span embedding, while the PBW identity U(L) = F⟨X⟩ and the product formula are in its proof, credited to Reutenauer, and are classical. The candidate's phrase "states the weighted Hall/PBW embedding" slightly over-attributes.

- **O6. Notation.** In §5, m denotes both the cut and the representation dimension. Rename one of them.

- **O7. Wording in §2.** "Disjoint source/target configurations" would read better as "each X_d is a partial-permutation matrix (at most one 1 per row and per column)". That property is what gives multiplicity 1 and the deterministic paths.

## Do-not-confuse checks requested by the brief

- **Semigroup effectiveness vs. linear injectivity.** The candidate proves linear coefficient extraction (a delta entry for each word) over every field, not merely that word images are distinct. ✔
- **Homogeneous vs. full injectivity.** Proved separately by level-grading disjointness (R7). ✔
- **Boolean vs. field.** Paths are unique, so entries are integers 0/1 and the extraction holds over any field. ✔
- **Target weakening.** None: all fields, all N ≥ N0, the infinite alphabet and unbounded class are retained. ✔

## Validation actually run (finite, not proof)

All runs used disposable copies in `/var/tmp`. The original packet was used read-only. Details are in `replay-receipts.json` and `independent-check-result.json`.

- Hashes of `manifest.json`, `verify.py`, `candidate-008.md`, `scope-008.md` and `sources/preprints-tree.json` match the brief's anchors.
- On the original packet, the anchored author verifier with `--private --source-tree <realpath preprints-tree.json>` returns PASS (25 public files, 1 public directory, 43 private files, 13 private directories, source tree checked). Wrong manifest and wrong verifier anchors are rejected.
- All 19 author `controls.py` cases behave as intended on a copy.
- Reviewer source-tree controls: a mutated family-008 blob, a truncated flag and the truncated `sources/tree.json` are all rejected.
- Direct Git blob SHA1 of every private source file matches the complete-tree entry for its canonical path: 14/14, 13/13 and 12/12. This was not derived from receipt agreement.
- The author's `diagnostic-008.py` replays byte-identically.
- Reviewer-written `independent_check.py`, separate from the author's code, checks:
  - the partial-permutation structure;
  - dense product orientation;
  - extraction against every word of weight up to cap + 4, for caps ≤ 22;
  - three-cap rank equal to dim A_N for N ≤ 22 over Q, GF(2) and GF(3);
  - the counts, a_j ≤ ρ^j for j ≤ 400, and D_T ≤ K ρ^{T/2} for T < 400;
  - Witt inversion against Lyndon counts;
  - the n ≥ 36 threshold;
  - four mutation controls;
  - the O1 single-cap facts.

No mathematical inference is drawn from any hash or finite check. The all-N proof is R1–R11.

## Reading, proof and search limits

- **Read in full:**
  - the brief, `AGENTS.md`, `sources/upstream.json`, `candidate-008.md`, `scope-008.md`, `source-and-credit.md`, `reading-limits.md`, `formal-interfaces.md`, `checkpoint.md`, `provenance/seal-repair.md` and `verify.py`;
  - from the parent's directory, `parent-primary-screen.json` and `lewin-primary-receipts.json`;
  - from source 008, `01-introduction.tex` (all of it, including thm:main) and `04-deletion.tex` (all of it, including the terminal right-endpoint coefficient extraction in lem:deletion-kernel, lines 246–250, which I credit as an antecedent coefficient test).
- **Read in part:**
  - `REPRODUCE.md` (display partially truncated);
  - `controls.py` and `diagnostic-008.py` (read in part; the terminal display skipped 18 and 47 lines respectively; both were executed only on copies);
  - the head of `parent-verification.json` and the head of `manifest.json`;
  - lines 1–120 of `frontier/NEW-TEN-2026-10-14.md` plus grep hits;
  - lines 1–110 of `02-algebra.tex` (lem:low-weights, lem:lie-lattice with proof, and the statement of lem:free-fiber).
- **Not read:**
  - source 008 sections 03 and 05–08, the rest of 02, the preamble, figures, references and paper.pdf;
  - upstream `lean/docs/008.md`, which is catalogued in `CONTENTS.md`.

  The source theorems are stipulated and were not audited.
- **Primary literature:** I did not read Mazorchuk–Steinberg, Cagliero–Rojas, Burde–Eick–de Graaf, Lewin, Lo–Ostheimer, or any truncated path-algebra literature for this proof gate. I performed no search, so I have no novelty or prior-art opinion. I did not open the parallel contribution packet or brief; I only saw its filename in a directory listing.
- **Proof limits:** R1–R11 cover the full scope. PBW, the free-Lie embedding over a field, and base change of free Lie algebras are used as classical facts. No formal verification was done.

## Seal

`manifest.json` lists every file in this directory except itself, plus the exact (empty) directory list. Authentication requires a caller-supplied external manifest SHA256. The caller must also check `verify.py` against its row in that anchored manifest *before* executing it, because a modified verifier can always accept itself. `controls.py` runs copied mutations under `/var/tmp`, including root, ancestor and internal symlinks, an outgoing hardlink, a FIFO, extra files and directories, edits, deletion, verifier edits and self-reseal. The external manifest anchor and final control results are reported in the hand-off message, not stored here.

## Contribution

This review gives no contribution verdict; that gate is separate. Its only contribution-relevant observation is O1.
