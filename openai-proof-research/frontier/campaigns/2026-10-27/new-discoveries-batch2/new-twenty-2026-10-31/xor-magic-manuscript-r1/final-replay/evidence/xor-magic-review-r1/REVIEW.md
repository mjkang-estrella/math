# Independent adversarial review: MathDB 372205 (arXiv:2512.19278, Conjecture 25)

Reviewer lane: xor-magic-review-r1. Date: 2026-11-02 UTC (2026-11-01 Los Angeles). No child agents, no git, no shared-ledger edits, no uploads or messages. All writes stayed in this lane. xor-magic-formal-r3 was not touched. Credit: 0. This is a review, not an acceptance.

The 286 input files were hash-bound before and after the work, with an unchanged aggregate of `0d0d7a3d…15c0f1`. PROOF.md and the r2 zip match the pinned SHA-256 values.

## Verdicts

| Gate | Verdict |
|---|---|
| A. Source fidelity and scope | QUALIFIED_PASS |
| B. Ordinary mathematics | PASS |
| C. Partial Lean packets (r2 replay and fidelity) | PASS as a partial packet; not a solution |
| D. Prior art | QUALIFIED_PASS (Batal's article body unread) |
| E. Significance | QUALIFIED_PASS |

Recommendation: continue the formalization. There is no credit until a kernel-checked endpoint proves both `∀ n ≥ 4, ¬ PrintedAt n` and `∀ n ≥ 4, CorrectedAt n`, with a fresh strict extracted replay.

## A. Scope

The source definition requires:
- a simple, connected graph of order 2^n;
- a bijective labelling onto (Z_2)^n;
- zero open or closed neighbourhood sums.

Conjecture 25 does not quantify n. The context fixes n ≥ 4 (Theorem 5 is stated for n > 3).

The printed closed list {4, …, 2^n-6, 2^n-4} contains 2^n-4, which Proposition 24 forbids. So the printed statement is false for every n ≥ 3; at n = 3 the closed list is {4} = 2^3-4. I re-proved the obstruction by hand. The complement of such a graph is cubic and open-zero. At a neighbour of the label-0 vertex, the two remaining neighbours would need equal labels, which contradicts injectivity. The argument does not use connectivity.

Several things show that the corrected range is the intended statement:
- The printed open list is exactly the odd degrees not excluded by Proposition 24.
- Under Observation 1 (d ↦ 2^n-1-d), the open list maps to closed {4, …, 2^n-6}, not {4, …, 2^n-4}.
- Theorem 18 at n = 4 stops at 10 = 2^n-6, and Section 4 calls this "each possible degree".
- MathDB's own sentence says the conjecture completes the picture "apart from the degrees excluded by the previously stated nonexistence result".

Section 4 has two more typos: the exclusion set {0, 2, 2^n-2, 2^n}, and "odd degree" used for an even list. Neither counts as a discovery.

Judgement: the literal negation together with the corrected theorem is a full resolution of the problem's intended scope. It is not a zero-credit endpoint correction, because the correction deletes only one degree that the source itself already forbids, and all the substantive existence content is what gets proved. Root must present the credited claim exactly in this form.

MathDB's wording omits "connected". The existence direction is unaffected. For the negation, I proved a connectivity-free obstruction in Lean (see C).

## B. Mathematics

I checked every lemma by hand and with code written from scratch (`scripts/xm.py`). My code chooses c at random in ker B, unlike the focused lane's deterministic first-basis-vector rule.

- **Lift lemma.** The labelling is a bijection onto F2^(n+2). The linear coefficient is (d-2) + w + w^-1 + ε ≡ d-1+ε ≡ 0 (mod 2). This needs every cycle of F oriented so that each vertex has one F-edge in and one out. The constant term is Bc, where column e of B is 1 at the tail and a^-1 at the head. Both ker D = 0 and rank B = m follow from the w^L transport. So dim ker B = (d/2-1)m ≥ m.
- **Dimension count.** For each edge, the BD entry is exactly 1, so BD ≠ 0. That gives dim(im D ∩ ker B) ≤ m-1. Measured values (dim ker B versus the intersection):
  - closed, d = 4: 16 vs 8 at m = 16; 32 vs 6 at m = 32; 64 vs 12 at m = 64;
  - open, d = 5: 24 vs 6; 48 vs 6; 96 vs 10.
  - The d = 4 boundary therefore holds with margin.
- **Holonomy.** The translation subgroup is normal and stable under t ↦ wt, so it has order 1 or 4; order 2 is impossible. With no translations, H is cyclic of order 3 with a common fixed point. That point transports to a section b with c = Db, which contradicts the choice of c.
  - I tested "connected ⇔ c ∉ im D" in 160 control lifts: c = 0, c in im D ∩ ker B, and random c in ker B. Every one agreed.
- **Persistence.** The lifted complement splits into 3 + 3d + 4(m-1-d) = 4m-1-d perfect matchings. I verified this exactly at every lift level built. The distinguished cycle lifts to lengths L and 3L. Observed examples:
  - [16] → [16, 48];
  - [8, 8, 16] → [8, 8, 16, 24, 24, 48];
  - at the second level, [16, 48] → [16, 48, 96, 96].
- **Interpolation.** The degree is d+2k+4j, and these values cover every degree of the right parity in [d, 4m-4-d]. Label sums are preserved. Connectivity holds for k = 0 (the graph contains the lift) and for k > 0 (K4,4 minus a matching is the cube, which is connected).
- **Complements and induction.** The endpoints come from complements: open N-5 and N-7 from closed 4 and 6, and closed N-6 from open 5. The induction runs n → n+2 in both parities.

Independent computations (corroboration, not proof):

| n | Degrees verified | Notes |
|---|---|---|
| 6 | 56 of 56 | every corrected degree |
| 7 | 120 of 120 | every corrected degree |
| 8 | 248 of 248 | two lift iterations, 16 → 64 → 256 |
| 9 | 51 of 504 | every endpoint, plus 40 random degrees |

Every graph listed was checked to be simple, regular, zero-sum and connected.

At orders 16 and 32, I checked every base witness and complement independently. The author files were parsed by AST literals, never executed. Every corrected degree is covered, and the seed matching certificates are valid.

Objections (exposition only):

1. PROOF.md attributes the n = 4 closed-6 and n = 5 closed-4 cases to complements. Those complements have degree below N/2, so the high-degree lemma does not apply. They are in fact connected (verified here), and the Lean bases have direct certificates.
2. The equivalence "the holonomies form a group, and connectivity ⇔ transitivity" is used without proof.

## C. Lean r2 packet

- **Extraction.** Fresh extraction into `work/replay-r2` with my own driver (`scripts/lean_replay.py`); the packet's own `replay.py` was not run.
  - The zip's SHA-256 matches the pinned value.
  - All 72 members are regular files with relative paths.
  - The zip contained no oleans.
  - All 48 Lean sources are byte-identical to the lane's copies.
- **Strict build.** Lean 4.34.1 (commit 5045d005…). All 48 modules build with `-j1 -DwarningAsError=true`, each call under its own cap scope. The peak was 29.9 s wall and 5.06 GB sampled private RSS.
- **leanchecker.** 48 of 48 pass.
- **My own audit** (`lean/ReviewAudit.lean`) covers 780 declarations, 502 of them theorems. None is an axiom, opaque, unsafe, partial, `implemented_by` or `extern`. Transitive axioms are only propext, Classical.choice and Quot.sound.
- **Negative controls.** All six packet controls fail for the stated reason. My two extra controls also fail as intended:
  - the degree-10 witness does not inhabit `ClosedExists 4 12`;
  - `PrintedAt 4` cannot be obtained from `CorrectedAt 4`.
- **Definitional fidelity.** `Bits`, `OpenMagic`, `ClosedMagic`, `OpenExists`, `ClosedExists`, `PrintedAt` and `CorrectedAt` faithfully render the source definitions and both statements. I found no weakening. Notes:
  - The packet's negations instantiate only n = 4.
  - My `lean/ReviewControls.lean` compiles strictly with the standard axioms and proves:
    - `∀ n ≥ 3, ¬ PrintedAt n`;
    - a connectivity-free version of the 2^n-4 obstruction;
    - `CorrectedAt 4 ∧ CorrectedAt 5 ∧ ¬ PrintedAt 4 ∧ ¬ PrintedAt 5`.
  - There is no universal or conditional `CorrectedAt` theorem, as GAPS.md honestly says.

## D. Prior art

What I read:
- 2512.19278 v1 (re-fetched: still only v1).
- Batal, arXiv:2609.05934 (September 2026). It does not cite 2512.19278 or treat Conjecture 25; its XOR-magic paragraph is only about row-separation characterisations.
- Siehler 2019, author copy. It covers cubic closed graphs only.
- Batal's GCGT 2026 abstract. It covers the other parity class: closed odd degrees 3 … 2^n-5 and 2^n-1, plus nonexistence for 2^n-3.
- Two 2026 abstracts by Cichacz, Grochowski and Zuazua. They claim only Theorem 5-level existence.

What stayed unread:
- The body of Batal's DAM 2026 article. The ScienceDirect 403 route was not retried; the IYTE repository returned an Anubis bot challenge, which I did not solve or retry; no arXiv version exists; a ResearchGate item was seen in search results but not fetched.
- OpenAlex's "cites" lists are empty, but incomplete, so they are not clearance.

Registries (HEAD identity only):
- openai/math HEAD is `4eaee875…`, unchanged.
- Omega HEAD is now `da784eaf…` (2026-11-02T02:10Z); its latest change is unrelated.

I found no existing all-degree construction. Batal posed odd-open and even-closed existence as an open problem, so his paper cannot contain the result.

## E. Significance

Qualified pass. The result settles the source's only conjecture, in its intended form, for every n and every degree. With Proposition 24 it gives a complete if-and-only-if picture within the parity classes. The source's own tools (products, complements and MILP bases) leave large gaps; at n = 8, for example, the source lists only open degrees 9–21 plus sporadic high degrees. The F4 affine lift is a new uniform mechanism, so the result is not a routine corollary, padding or a parameter instance.

The qualifications:
- the problem is recent and from a small community, and the proof is short;
- credit depends on root accepting the scope framing in A;
- credit also depends on the missing Lean endpoint;
- Batal's article body is unread.

## Hazards the formalization must avoid

- **H1.** The distinguished cycle needs length ≥ 3 and must be a genuine cycle of F. A back-and-forth closed walk of length 2 satisfies 3 ∤ 2 but has trivial holonomy.
- **H2.** Every cycle of F must be oriented consistently, and the distinguished cycle traversed in that orientation. Otherwise the holonomy scalar is w^(fwd-bwd). All non-F edges must have slope exactly 1.
- **H3.** B and D must use the same oriented edges. The reverse edge map is a^-1 x + a^-1 c. The nonzero BD witness needs simplicity. Use |E| = dm/2 ≥ 2m.
- **H4.** The lifted complement must be split into exactly 4m-1-d disjoint matchings that cover it. The next distinguished cycle is the fixed-point lift.
- **H5.** Interpolation connectivity needs separate k = 0 and k > 0 arguments. Full blocks go over base-complement matchings only.
- **H6.** Base complements of degree below N/2 need direct connectivity certificates.
- **H7.** The induction runs n → n+2 from n = 4 and from n = 5 separately; the interpolation base needs n ≥ 6.

## Artifacts

- `review.json` — machine-readable verdicts, objections and next actions.
- `scripts/` — `xm.py`, `verify_base.py`, `lift_check.py`, `lean_replay.py`, `capped.py`, `hashbind.py`, `fetch.py`.
- `lean/` — the reviewer audit, positive controls and negative controls.
- `outputs/` — base verification and lift results for n = 6, 7, 8 and 9.
- `receipts/` — input hashes before and after, per-call cap receipts, Lean replay state, web receipts.
- `logs/` — logs for every call.
- `work/` — the fresh extraction (with built oleans) and the fetched web bodies, kept as untrusted data.

No background jobs remain from this lane. The Lean processes visible on the machine belong to the sibling r3 lane.
