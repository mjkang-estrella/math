# Independent fidelity review: candidate 388087 (Király, orientation of nonideal clutters)

Reviewer: Claude Opus 5.5, independent review sub-agent, 2026-10-31 local (2026-11-01 UTC). I am not the author.

Scope:
- I wrote only in `kiraly-fidelity-review-r1/`.
- No git, no subagents, no shared or ledger edits, no publication, no browser, no network fetches.
- All checks ran with at most 2 CPUs (`taskset -c 0,1`, `nice`, timeouts).

Candidate under review:
- `candidates/kiraly-clutter-v1` (`packet.zip` sha256 `6b23d198…c202`)
- `KiralyCounterexample.lean` sha256 `1370129f…cddbb`

Author lane: `clutter-characterization-r1`.

## Verdict

**No fatal issue found.**

| Gate | Verdict |
|---|---|
| 1. Literal source fidelity | **PASS** |
| 2. Mathematical fidelity | **PASS** |
| 3. Strict Lean replay | **PASS**, with documented reproducibility limits (non-blocking) |
| 4. Claim scope / package | **PASS**, with minor non-blocking packaging and wording notes |

**Recommendation: fidelity PASS.** This is conditional on the remaining separate acceptance gates:
- the novelty/significance review (queued next);
- the paper (pending);
- root adjudication.

This review grants no discovery credit, no novelty approval and no accepted count.

## Hash discipline (before/after)

- **Before work:** all 81 entries of `input-bindings.json` matched (sha256 recomputed by me).
- **After work:** all 81 still match (`logs/bindings-after.txt`: 0 mismatches).
- `input-bindings.json` sha256: `b2e40ed7e591a885d981b7ad751fdbb481a41dc5b1c1e30419d37af79234005a`
- `launch.json` sha256: `5007c666ddd8601c12437e1c787bae2e89ab5c2f6534aade20f4624499445bc8`
- I modified no author or candidate file.
- The fresh extraction of `packet.zip` is byte-identical to the six loose candidate files, and `manifest.json` hashes verify (`logs/extracted-sha256.txt`).

## Gate 1: literal source fidelity (PASS)

### Sources recovered (all local, hash-checked)

**1. MathDB 388087 record.**
- Location: `lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0015.jsonl`, line 987.
- Line sha256 (with newline): `ee6b4fba…31e`. Statement sha256: `a14224a5…141e`. Both match `targets.json`.
- Status: open, 0 solutions.
- `documented_by_source_url`: `https://egres.elte.hu/tr/egres-10-09_November_2010.pdf`.
- Statement, verbatim:
  > Let 𝒞 be a clutter on ground set V, and let ℬ be its blocker. Is it true that 𝒞 is nonideal if and only if there exist p:𝒞→V and q:ℬ→V such that p(X)∈X for every X∈𝒞, p(Y)∈Y for every Y∈ℬ, if p(X)=q(Y), then |X∩Y|>1?

**2. Egres Open page.**
- File: `lane-1/sources/egres/Orientation_of_nonideal_clutters.html`, sha256 `047b7108…58b9`. It is a Wayback snapshot (2020–2024) of page oldid 1782, last modified 2 Jan 2015.
- The text is identical to MathDB, including the `p(Y)∈Y` typo.
- Remarks on the page:
  - The conjecture is due to T. Király.
  - Polyhedral Sperner shows "no such functions exist for ideal clutters".
  - It reduces to mni clutters.
  - Pap proved the cyclic-core case.
- Reference given: Pap's PhD thesis.

**3. Pap, EGRES TR-2010-09.**
- File: `sources/egres-tr-10-09.pdf`, sha256 `48b900cf…090a`. I extracted it myself with `pdftotext -layout`; my text is byte-identical to the author's `runs/egres-tr-10-09.txt`.
- Conjecture 1.2:
  > Let A be a nonideal clutter on ground set S and let B be its blocker. Then there exists a function h : A ∪ B → S such that h(X) ∈ X ∀X ∈ A ∪ B and if h(A) = h(B) for some A ∈ A and B ∈ B then |A ∩ B| > 1.
- Definitions:
  - A clutter is a set family on a finite ground set with no set containing another.
  - The blocker is the family of inclusion-minimal transversals.
  - P(C) = {x ∈ ℝ^S_+ : x(C) ≥ 1 ∀ C ∈ 𝒞}.
  - 𝒞 is ideal iff P(C) is an integer polyhedron.

**4. Pap, PhD thesis 2015.**
- File: `sources/wb-pap-julia-2015.pdf`, sha256 `8f4bf63b…a3c2`. My extraction is byte-identical to the author's `runs/pap-thesis.txt`.
- Conjecture 3.4.5:
  > Let A be a clutter on ground set [n] and let B be its blocker. Then A and B are nonideal if and only if there exist functions p : A → S and q : B → S such that (i) p(A) ∈ A …, (ii) q(B) ∈ B for every B ∈ B, and (iii) if p(A) = q(B) … then |A ∩ B| > 1.
- §1.4 definitions are as in the TR. It also says "C is called ideal if the polyhedron P(C) is integer".
- Theorem 3.3.22 (ideal ⇒ no (p, q)) uses `q(B) ∈ B` explicitly.
- Theorem 3.4.7 is the core-restricted statement on Ā, B̄. The overbars are lost in text extraction; the TR's Claim 2.5 states h : Ā ∪ B̄ explicitly, and the thesis says "true if we restrict it to the cores".

### The `p(Y)∈Y` typo: the correction to `q(Y)∈Y` is forced

1. **The literal text is ill-typed.** p is defined only on 𝒞, and for C11 we have 𝒞 ∩ ℬ = ∅ (verified), so p(Y) is undefined for every Y ∈ ℬ.
2. **The alternative reading is degenerate.** If the clause is dropped and q is left unconstrained, the ideal path {01, 12} admits p = (0, 2), q ≡ 1. That contradicts the proved Sperner direction stated in the Egres remark itself.
3. **Both Pap sources use the corrected form.** The thesis has `q(B) ∈ B`; the TR has h(X) ∈ X for all X ∈ 𝒜 ∪ ℬ.
4. **Under the degenerate reading the "conjecture" is trivially false** by the path example, so it is not a meaningful target.

The candidate therefore addresses the genuine intended conjecture. This is not an excluded endpoint or domain correction:
- no hypothesis was weakened or strengthened;
- the credit sought is for refuting the intended statement, not for the correction.

### Variant forms: exact logical relationship needed for refutation

| Source form | Relationship to the Lean result | Status |
|---|---|---|
| Egres/MathDB: 𝒞 nonideal ⇔ ∃ p, q (with q(Y)∈Y) | Literally `KiralyConjecture`; refuted by `kiraly_conjecture_false`. | Lean |
| Pap TR Conj. 1.2: nonideal ⇒ ∃ h : 𝒜 ∪ ℬ → S (one direction) | Existence of h implies existence of (p, q) (restrict h), for every clutter, with no disjointness needed. So nonideal ∧ ¬∃(p, q) refutes it. | Reviewer-proved in Lean (`singleH_imp`, `no_singleH`, `scripts/ReviewAudit.lean`), axioms [propext, Classical.choice, Quot.sound]. Not in the candidate packet. |
| Pap thesis 3.4.5: "𝒜 **and ℬ** nonideal" ⇔ ∃ p, q | Equivalent to the Egres form because 𝒞 is ideal iff b(𝒞) is ideal (Lehman). | Reviewer exact check: (1/4)·**1** is a vertex of P(b(C11)) (11 tight 4-set constraints of rank 11; 5-sets give 5/4 > 1). Not formalized; not needed for the MathDB form. |
| One-directional nonideal ⇒ ∃(p, q) | `counterexample` gives IsClutter ∧ ¬IsIdeal ∧ ¬KiralyProperty directly. | Reviewer `example` in the audit file. |

The author's claim that "single h is equivalent here because 𝒞 ∩ ℬ = ∅" is correct (verified). Only the implication h ⇒ (p, q) is actually needed, and it holds unconditionally.

### Quantifiers and side conditions

All hold for C11, so no reasonable reading excludes the instance:
- finite ground set (Fin 11);
- every ground element is used (each lies in exactly 3 edges);
- 𝒞 is nonempty, with no empty and no singleton edges;
- edges are distinct and pairwise incomparable;
- the blocker contains no singleton.

The minor provisos in the sources ({s} ∉ 𝒞, etc.) concern only the reduction claims and are irrelevant here.

### Ideality definition

The Lean `IsIdeal` says every point of `Set.extremePoints ℝ (coveringPolyhedron C)` has integer coordinates.

P(C) ⊆ ℝ^V_+ contains no line, so it is pointed, and its extreme points are exactly its vertices. For pointed rational polyhedra, "integer polyhedron" ⇔ "all vertices integral".

A general Lean equivalence is not needed. The refutation exhibits a non-integral **extreme point** x* = (1/3, …, 1/3) of the genuine real polyhedron, and that alone defeats every standard definition of ideality:
- **P = conv(P ∩ ℤⁿ) + cone:** the extreme points of such a set are integral.
- **Every minimal face contains an integer point:** the face {x*} contains none.
- **min{wx : x ∈ P} has an integral optimum for all w ≥ 0:** take w = 1, the all-ones vector.
  - Over P, w·x = Σ_X x(X)/3 ≥ 11/3, because every vertex lies in exactly 3 edges. Equality forces all 11 edge constraints tight, hence x = x* by nonsingularity.
  - So x* is the unique optimum, and it is non-integral.
- **Pap's P = conv{χ_B : B ∈ b(C)} + ℝ^S_+:** x* would have to be some χ_B.

The direction (ideal ⇐ …) of the Lean iff is never used, so its faithfulness is irrelevant to the refutation.

## Gate 2: mathematical fidelity (PASS)

### Independent reviewer computations

These were written from scratch, without author code: `scripts/audit.py`, `scripts/extra.py`, `scripts/sanity.py`; logs in `logs/*.json`.

**Clutter properties:**
- C11 is a clutter: 11 distinct, pairwise incomparable 3-sets.
- Ground set covered; all degrees are 3.

**Blocker:**
- Computed by definition over all 2¹¹ subsets, with full proper-subset minimality cross-checked against one-element-erasure minimality.
- |b(C11)| = 36: 11 four-sets and 25 five-sets.
- The Lean `YL` list equals the full blocker exactly (parsed from the source).
- b(b(C11)) = C11.
- 𝒞 ∩ ℬ = ∅.

**Fractional vertex:**
- The incidence matrix is 11×11 with exact rank 11 and determinant 3.
- x* is feasible, with all 11 edge constraints tight, so it is the unique solution of the tight system: a vertex of real P(C11).

**Lehman structure:**
- A·B̄ᵀ has entries in {1, 2}, with exactly one 2 per row and per column.
- So A·B̄ᵀ = J + P for a permutation P (Lehman form J + dI with d = 1 after reindexing).

**No (p, q):**
- Brute force over all 3¹¹ = 177,147 choices of p.
- For each, q is decoupled per blocker member Y: v ∈ Y is forbidden iff some edge X has X ∩ Y = {v} and p(X) = v. Because Y is a transversal, X ∩ Y ≠ ∅, so `p X = q Y ∧ |X∩Y| ≤ 1` is equivalent to this.
- Result: **0** choices of p admit a valid q, using the full 36-member blocker.

**Author diagnostics confirmed:**
- With only the 11 core 4-sets in place of the blocker, a valid (p, q) exists. This is consistent with Pap Thm 3.4.7: the failure is caused by the 25 five-sets.
- Dropping any one of the 36 blocker members makes the instance satisfiable (36/36). So all 36 are needed, confirming the author's claim that the minimal unsatisfiable core is the whole blocker.

**Core is not cyclic:**
- Pair-multiplicity profile: C11 has {1: 15, 2: 9}; C₁₁³ has {1: 11, 2: 11}.
- An exhaustive backtracking isomorphism test against C₁₁³ returns false.
- This is consistent with Pap Thm 3.4.9, which would otherwise contradict the result.

**Solver controls:**

| Instance | Valid (p, q) exists? | Expected by |
|---|---|---|
| C₁₁³ (cyclic) | yes | Pap Thm 3.4.9 |
| C₅² | yes | |
| Fano | yes | |
| J₃ | yes | |
| path | no | Sperner direction |
| C₄ edges | no | Sperner direction |
| C₆ edges | no | Sperner direction |

So the solver is not vacuous.

### Why the 36 blocker memberships suffice (exhaustive blocker equality is not needed)

`KiralyProperty C` requires q on **every** member of `blocker C`. If (p, q) existed, q restricted to any subset S ⊆ b(C) would still satisfy (ii)–(iii) on S. Proving that no p admits a valid q on S therefore refutes the property for b(C).

Soundness needs only S ⊆ b(C), which `Y_mem_blocker` proves for all 36 sets:
- transversality: `transversal_Y`;
- minimality: each one-element erasure misses some edge (`minimal_Y`), and transversality is upward-closed, so every proper subset is a non-transversal.

Exhaustiveness (S = b(C)) is true, as I checked independently, but it is logically unnecessary.

### Audit of the Lean proof internals

- **`chk_sound`.** By induction on the tree:
  - At a leaf, `deadB` returns true only if j < |K| and every entry (v, is) of K[j] has some i ∈ is with (i, v) in the assignment. Every assignment pair agrees with b, so b i = v.
  - At a node, `D.getD i [] = [d0, d1, d2]`, b i ∈ D[i] (by hypothesis), and the three subtrees are checked under the extended assignment. A malformed D entry makes `chk` return false.
  - The statement quantifies over all b : ℕ → ℕ that respect D. This is sound.
- **Data bridge.** Kernel `decide` proves:
  - `fact_dom`: elements of X'_i, as `val`s, lie in DL[i];
  - `fact_cover`: every y ∈ Y'_j appears as e.1 for some e ∈ KL[j];
  - `fact_single`: each listed edge index i is < 11 and |X'_i ∩ Y'_j| ≤ 1.

  Only these directions are needed: KL entries are genuine singleton intersections, and KL covers Y_j.

  In `not_kiraly`, b i := (p X_i).val for i < 11 and 0 otherwise. Out-of-range i has DL.getD = [], so the hypothesis of `chk_sound` is vacuous there; this is correct handling of the default.

  The certificate yields j < 36 with Y_j fully killed. `fact_cover` applied to q(Y_j) gives an edge X_i with p X_i = q Y_j (via `Fin.ext` on vals) and |X_i ∩ Y_j| ≤ 1, contradicting (iii).
- **Fin wraparound.** All Fin 11 literals in XL and YL are ≤ 10, so nothing wraps. The parsed lists equal the integer edges and blocker exactly.
- **No vacuity.** `IsClutter` is only a hypothesis, discharged for C11. `blocker` is exactly the minimal transversals, neither broader (which would make refutation easier) nor narrower. `coveringPolyhedron` is the standard real polyhedron. q ranges over the entire `blocker C` subtype and p over the entire `C` subtype. No definition is inconsistent; C11 instantiates every hypothesis nontrivially.
- **`xstar_extreme`.** It uses Mathlib's `mem_extremePoints` (an extreme point is one that lies in no open segment of two other points of the set) in the real vector space `Fin 11 → ℝ`. If x* = a·y + b·z with a, b > 0 and a + b = 1, then `tight` forces every edge sum of y and z to equal 1, and `eq_xstar` (the 11 linear equations, solved by `linarith`) forces y = z = x*. This is genuine real geometry, not a finite model.

## Gate 3: strict Lean replay (PASS)

**Toolchain and pins:**
- Lean: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, version 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, binary sha256 `e8baaa71…5550`.
- `lean-toolchain` is `leanprover/lean4:v4.34.1`.
- The candidate's `lake-manifest.json` is byte-identical to `campaigns/2026-10-14/formal/lake-manifest.json` (sha256 `d00ceb5c…bb8`).
- The package `.git/HEAD` files, read as files with no git commands run, match the manifest:
  - mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
  - batteries `f2effa3d…`
  - aesop `355695d5…`
  - Qq `6a489d9a…`
  - plausible `118aa17e…`
  - proofwidgets `106ff4fa…`
  - importGraph `e928b725…`
  - LeanSearchClient `ddf04cf3…`
  - Cli `e92c9f15…`

**Source scan** (`logs/token-scan.txt`):
- The only import is `import Mathlib`.
- No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by`, `extern`, `opaque`, `ofReduceBool`, `set_option`, `instance`, `macro`, `elab`, `syntax`, `attribute`, `#eval` or `run_cmd`.
- The only hits are `noncomputable def xstar` (benign) and the word "partial" inside a doc comment.
- No source premise is smuggled in: every hypothesis used is proved in-file.

**Fresh-extraction strict build:**
- Command, run in `replay/extracted/` after `unzip packet.zip`:
  ```
  env -i HOME=$HOME PATH=/usr/bin:/bin LEAN_PATH="$(cat leanpath.txt)" \
    taskset -c 0,1 nice lean -DwarningAsError=true -o KiralyCounterexample.olean KiralyCounterexample.lean
  ```
- Result: rc 0, 16.9 s, empty stderr.
- stdout (`logs/build.stdout`):
  ```
  'KiralyClutter.kiraly_conjecture_false' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KiralyClutter.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
- olean sha256 `dbe37e0818c25358741985928c916242a992796c3b353a1f6ee0830d8431beb4`. This is identical to the author's and the parent's, so the build is deterministic.

**Reviewer audit file** (`scripts/ReviewAudit.lean`, imports the rebuilt module; rc 0; `logs/review-audit.out`):
- `#print` of every definition matches the text above.
- `#check` of the endpoints gives:
  - `kiraly_conjecture_false : ¬KiralyConjecture`
  - `counterexample : IsClutter C11 ∧ ¬IsIdeal C11 ∧ ¬KiralyProperty C11`
- A `run_cmd` scan over all 104 declarations of module `KiralyCounterexample` found **0 axiom declarations**. No declaration depends on any axiom outside {propext, Classical.choice, Quot.sound}. This covers `cert_ok` and every `decide +kernel` lemma, so there is no `Lean.ofReduceBool` or `trustCompiler` anywhere.
- The bridge theorems `singleH_imp` and `no_singleH` and the one-direction refutation compile, with axioms [propext, Classical.choice, Quot.sound].

**Independent kernel replay:**
- `leanchecker KiralyCounterexample` (Lean 4.34.1 `leanchecker`, `replayFromImports` mode), clean env: rc 0 in 14 s (`logs/leanchecker.out`).
- Negative control: a nonexistent module gives rc 1, "Could not find any oleans".

**Parent receipt:** `kiraly-parent-replay-r1/result.json` (sha256 `1c40362e…be48`) reports rc 0 with the same axiom output. I reproduced it independently and did not rely on it.

**Honest limits (non-blocking):**
- The replay depends on the local prebuilt Mathlib oleans in `campaigns/2026-10-14/formal/.lake`.
  - Their contents are not hash-pinned; only the package HEAD SHAs were checked.
  - They are user-writable (for example, `Mathlib.olean` has mode `rw-------`), so "read-only" holds by convention only.
- `leanchecker` was run in module mode, not `--fresh`, so Mathlib itself was not re-replayed.
- `leanpath.txt` lists one directory that does not exist (`packages/Cli/.lake/build/lib/lean`). This is harmless, since Mathlib does not import Cli.
- The packet has no lakefile. The copied manifest is named `frontier_support`, so `lake build` from the packet alone is impossible; replay uses raw `lean` with `LEAN_PATH`. This is documented in `metadata.json` ("portability").

## Gate 4: claim scope and package (PASS)

**Formal claims, all exact:**
- C11 is a clutter.
- C11 is not ideal.
- C11 has no Király (p, q).
- The Egres/MathDB iff conjecture is false.

**Not formal, and not promoted as formal:**
- Minimal nonideality (`metadata.json`: "external diagnostic only; not formalized or needed").
- The blocker count of 36.
- The (14, 3, 5) observations (explicitly "not claimed").
- Novelty (search-based caveat stated; access gaps on Lütolf–Margot disclosed).

**Non-blocking notes for a future revision:**

- **N1 (wording).** The Lean doc comment on `YL` says "they form the whole blocker". This is not a Lean theorem. It is true (reviewer exhaustive check), but should be labelled a diagnostic.
- **N2 (scope).** The SUMMARY outcome line says "in fact minimally nonideal". I did **not** independently verify mni, beyond the Lehman J + P structure, b(b(C)) = C and the blocker's fractional vertex. The MPR Table 3 claim was not checked by me. This must remain an unreviewed author diagnostic in any paper.
- **N3 (optional formal additions).** Consider adding to the packet:
  - the one-directional refutation;
  - the single-h bridge, already proved here in `scripts/ReviewAudit.lean`;
  - optionally, the nonideality of b(C11) via the (1/4)·**1** vertex.

  These would cover the Pap TR and thesis wordings formally. They are not required for the MathDB/Egres form.
- **N4 (reproducibility).** Bundle a lakefile pinning the mathlib revision, or document the local-olean dependency in the paper's artifact section.
- **N5 (deferred).** The live Egres page was not re-checked (only an archived snapshot; live hosts timed out per the author). Novelty and significance are explicitly deferred to the queued review.

## Exact theorem-to-source mapping

| Lean | Source |
|---|---|
| `IsClutter C` | "no set of it contains another" (TR §1; thesis §1.4) |
| `IsTransversal C T` | "intersect each set in C" (TR §1; thesis §1.4) |
| `blocker C` | "(inclusionwise) minimal transversals" (TR §1; thesis §1.4) |
| `coveringPolyhedron C` | P(C) = {x ∈ ℝ^S_+ : x(C) ≥ 1} (TR Def. 1.1; thesis §1.4) |
| `IsIdeal C` | "P(C) is an integer polyhedron" (TR Def. 1.1), via extreme points of a pointed polyhedron |
| `KiralyProperty C` | ∃ p : 𝒞 → V, q : ℬ → V, (i) p(X) ∈ X, (ii) q(Y) ∈ Y [typo-corrected], (iii) p(X) = q(Y) ⇒ \|X ∩ Y\| > 1 (Egres/MathDB; thesis Conj. 3.4.5) |
| `KiralyConjecture` | ∀ finite V, ∀ clutter 𝒞: 𝒞 nonideal ⇔ KiralyProperty (Egres/MathDB 388087 verbatim modulo the typo) |
| `kiraly_conjecture_false` | negation of MathDB 388087 |
| `counterexample` | refutes the nonideal ⇒ orientation direction (also Pap TR Conj. 1.2, via the reviewer bridge `singleH_imp`) |

## Artifacts in this directory

| Path | Contents |
|---|---|
| `scripts/audit.py` | Independent blocker, vertex and no-(p, q) checks, plus the cyclic test |
| `scripts/sanity.py` | Solver controls |
| `scripts/extra.py` | b(C) vertex, core-only check, drop-one check |
| `scripts/ReviewAudit.lean` | Definitions printout, bridge theorems, module-wide axiom scan |
| `logs/` | All outputs, build logs, leanchecker log, token scan, binding checks |
| `extract/` | Reviewer's own `pdftotext` extractions |
| `replay/extracted/` | Fresh packet extraction and the rebuilt olean |
| `review.json` | Machine-readable verdicts |
