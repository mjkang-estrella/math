# Independent review of MathDB 326640

Verdict: **PASS gates 1–3. Gate 4 passes claim/package honesty, with novelty/significance PENDING. No acceptance credit recommended yet.** No source, mathematical, or Lean defect found. No frozen proof was changed. A paper and the separate significance/subsumption review remain outstanding. This does not change the campaign's accepted 1/20.

## 1. Literal and primary-source fidelity — PASS

Read the assigned and ancestor AGENTS.md files, SUMMARY.md, PROOF.md, full Majority.lean, package README/replayer/manifest/toolchain, literal record, and relevant primary definitions and proof bodies. The protected PDF was independently processed with `pdftotext -layout`; the result in `primary-extracted.txt` is byte-identical to protected majority.txt. Its first page explicitly identifies **arXiv:1311.0479v1 [math.CO], 3 Nov 2013**. Receipt used https://arxiv.org/pdf/1311.0479; version identity comes from the body, not an assumption that an unversioned URL is immutable. No other version is used to alter the target. PDF-generation metadata dated 2022 does not supersede the displayed arXiv version.

Literal MathDB record: corpus `mathdb-normalized-chunk-0003.jsonl`, line **1146**, raw-line SHA256 including newline **7a2ad6aba94a241e476df3908a15a728d12c8d38b6ae238d8438a96192fd0171**. Independently read the original corpus line and verified that hash. Full record and path are retained in `literal-326640.json`. Live MathDB was not queried again; its previously reported 403 is not bypassed. Review fidelity is to this literal record and the independently read primary body, not a claim about current website status.

Source mapping (line numbers in regenerated/protected text and frozen Lean):

| Source | Exact meaning | Lean |
|---|---|---|
| Section 2, text 72–112, 134–147, PDF pp.2–3 | Finite simple underlying graph; MODS minimizes cardinality with closed out-neighborhood coverage at least n/2 | `arc`, `cover`, `mem_cover`, lines 65–76; `gamma`, `gamma_minimum`, lines 201–216, 295–307 |
| Section 3, Proposition 3.8 proof, text 233–246 | Explicitly writes N⁺[S] = N⁺[S₁] ∪ N⁺[S₂]; confirms union semantics | `cover` uses existential membership, never degree sums |
| Section 4 opening, text 416–418, PDF p.6 | One directed arc per undirected edge | `IsOrientation`, `arc_orientation`, `orientation_representation`, lines 269–291 |
| Definition 4.1, text 432–437, PDF p.6 | Upper parameter is max over orientations of the inner minimum | `DOM`, `le_DOM`, `DOM_maximum`, lines 218–226, 308–313 |
| Proposition 4.9 and proof, text 562–587, PDF p.8 | Positive r≤s; identifies DOM=1 exceptions, but is not assumed by this proof | Endpoint retains actual DOM≠1; no substituted exceptional-case classification |
| Conjecture 4.10, text 590–599, PDF p.8 | DOM=2 if s≤r+2, otherwise ceil((s−r)/2), conditional on DOM≠1 | `exact_formula`, `mathdb_326640`, `ceiling_spelling`, lines 252–266, 316–322 |

The endpoint is literally

```lean
∀ (r s : ℕ), 0 < r → r ≤ s →
  DOM (R := Fin r) (S := Fin s) ≠ 1 →
  DOM (R := Fin r) (S := Fin s) =
    if s ≤ r + 2 then 2 else (s-r+1)/2
```

Positive s follows from 0<r≤s. No upper bound, parity assumption, orientation restriction, or extra mathematical premise is present. Naturals encode the source's positive part sizes; permitting empty parts would be a different graph convention and is not required by the primary positive-integer context.

The paper allows bidirected digraphs in its general preliminaries, but its *orientation* definition additionally requires edge/arc count equality. Every cross edge must contribute at least one arc, and equality prevents any second opposite arc. Lean's exclusive cross-pair condition is therefore exact. Its negation equivalence gives exactly one direction classically. The printed degree-description prose has an apparent ordering typo; explicit N⁺(u)={v:uv∈A}, d⁺(u)=|N⁺(u)|, the MODS definition, and supporting union proofs resolve direction without changing the target. The signed-function parameter is separate and unused.

## 2. Independent mathematics and Lean semantics — PASS

Independently derived the argument rather than relying on the parent's pass label:

For maximum row and column outdegrees a,b, all rs edges contribute exactly once, so rs≤ra+sb≤s(a+b). Since s>0, a+b≥r. If r<s and any R→S arc exists, then a>0 and ra+sb<s(a+b), giving a+b≥r+1. The chosen vertices exist because both parts are nonempty; Lean obtains actual maxima, with no distributional assumption.

For selected u∈R,v∈S, write the covered R-part as {u}∪N⁺(v) and the covered S-part as {v}∪N⁺(u). If u→v, u is newly inserted but v was already present. If v→u, the reverse holds. Thus the total is **a+b+1**, not a+b+2, in both directions. `pair_card` splits on the actual Boolean entry and uses disjoint part sums. Overlap among arbitrary sets is handled by `cover`, not by summing neighborhoods.

Let h=ceil((r+s)/2). When s≤r+2, h≤r+1, so the pair works. Positive order makes gamma≥1 for every orientation. The actual hypothesis DOM≠1 then yields DOM=2; no unproved source classification is used.

When s>r+2, k=ceil((s−r)/2)≥2 and h=r+k. In the nonexceptional orientation the pair covers at least r+2. If c<h vertices are currently covered and t≤2 vertices selected, add h−c uncovered vertices. There are enough because h≤r+s; the budget inequality h+t≤c+k gives t+(h−c)≤k. All added vertices cover themselves; monotonicity preserves previous coverage. `extend` chooses an actual finite subset of the complement of exactly this size and proves disjointness and union bounds.

If there is no R→S arc, choose k vertices of S. Here 1≤k≤s, so this is available and nonempty, and coverage is exactly R plus the chosen vertices. For the same all-S→R orientation, **every** selected T satisfies N⁺[T]⊆R∪T, hence |N⁺[T]|≤r+|T|; reaching h=r+k forces |T|≥k. This proves sharpness without assuming T lies in S.

Boundary checks are symbolic, not a finite proof search. At s=r, h=r; at s=r+1 and r+2, h=r+1, all covered by the weak pair bound. At s=r+3, h=r+2 and k=2, exactly the strict-pair threshold. For r=1 and s≥4, k=ceil((s−1)/2)=floor(s/2), matching the source star formula (Proposition 4.6, with n=s+1). For s=1,2,3 the star has DOM=1: some arc tail covers two vertices, already at least half of the at-most-four vertices, so these cases are correctly outside the conditional assertion. The other small source exceptions likewise occur only in the retained DOM≠1 branch exclusion. No false unconditional formula is asserted.

Semantic bridges checked in full:

- Every Boolean matrix describes a valid orientation, and `orientation_representation` recovers every relation satisfying the ordinary orientation conditions, with no finite-type hypotheses needed for that bridge. Relabeling a finite bipartite graph by Fin r⊕Fin s preserves arc and coverage cardinalities; this is ordinary isomorphism invariance, not a graph-class restriction.
- Every subset of the finite vertex type is a Finset. The extra review-only Lean example in `replay/SemanticAudit.lean` verifies, for an arbitrary Set X, that membership in `cover E X.toFinset` is exactly `v∈X ∨ ∃u∈X, arc E u v`. Thus arbitrary subsets, not only pairs or selected shapes, enter the minimum and lower bound.
- `gamma_exists` supplies a genuine witness (the whole vertex set). `Nat.find` is therefore a minimum of a nonempty feasibility predicate; `gamma_minimum` proves attainment at exactly gamma and minimality against every feasible T.
- The space of Boolean functions is finite and inhabited even for empty index types. `DOM_maximum` proves its sup is attained and bounds every gamma. There is no fallback/default maximum.
- `majority_criterion` states h≤|cover| iff r+s≤2|cover|, so equality at half is allowed. `ceiling_spelling` proves s−r≤2k<s−r+2; with r≤s, natural subtraction equals ordinary nonnegative difference and this is precisely the ceiling formula.

Inspected the complete theorem dependency chain: total, pair_bound/pair_strict, cover lemmas, pair_card, extend, sink_upper/lower, upper, gamma/DOM, exact_formula, and endpoint. Positivity/nonemptiness and strict r<s assumptions are supplied at their call sites. No hidden hypothesis was found. Propositions 3.8/3.10, 4.6/4.9, and Theorem 4.7 proof bodies were read for source context; none is imported as an assumed theorem in the certificate.

## 3. Fresh extracted strict replay — PASS

Independently extracted all five zip members into this review directory; no preexisting olean was present in the zip. Every member equals both the frozen packet file and the extracted copy byte for byte; see `independent-checks.json`. The extracted replayer checks the source hash, toolchain version and every manifest package revision by read-only metadata. It builds against the supplied external cache, with inherited Lean settings cleared, output directed here, process affinity restricted to CPUs 0,1 and `-j2`.

Reproduce from the workspace root:

```sh
taskset -c 0,1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/majority-fidelity-review-r1/extracted/packet/replay.py \
  --dependency-root /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages \
  --lean /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean \
  --output /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/majority-fidelity-review-r1/reproduce-output
```

Actual fresh run: **exit 0, 5.067475 seconds**, `-DwarningAsError=true`, empty stderr. Lean **4.34.1**, compiler commit **5045d0056413266e57c625dcd7c365b10e377c52**; mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**. Detailed package revisions, command, logs and times: `replay/result.json`, `replay/lean.stdout.log`, `replay/lean.stderr.log`.

All four exact named audit outputs independently inspected:

```
Majority.mathdb_326640              [propext, Classical.choice, Quot.sound]
Majority.orientation_representation [propext, Classical.choice, Quot.sound]
Majority.gamma_minimum             [propext, Classical.choice, Quot.sound]
Majority.DOM_maximum               [propext, Classical.choice, Quot.sound]
```

The review-only strict audit also printed theorem/bridge types and audited `pair_card`, `pair_strict`, and `extend`: each uses only those same three axioms. Its final run exits 0 with empty stderr. Two initial review-only Set-example elaboration errors (missing classical decidability, then missing noncomputable marking) were corrected in the review file; their logs are retained. They were not frozen-packet errors. No sorry/admit/added axiom/unsafe/native_decide/ofReduceBool occurs in frozen Majority.lean. `decide` in orientation representation merely encodes an arbitrary proposition as a Boolean; it is not a proof-search oracle.

This is a fresh theorem rebuild using **external prebuilt dependencies**, not an independent rebuild of all mathlib or a validation of its binary provenance. All pinned revision metadata agrees. Optional leanchecker was not independently run; the author/parent's checker claims are not adopted as evidence here. The independent Lean kernel replay is sufficient for this gate's requested replay, with that explicit cache trust boundary.

## 4. Scope and credit — honesty PASS; qualification PENDING

SUMMARY.md and PROOF.md explicitly claim zero worker credit, retain DOM≠1, describe a structural all-sizes result, and flag the elementary proof's significance question. That description is accurate. A named conjecture and a closed Lean proof do not establish novelty or significant new mathematics. The all-orientation sharp formula is proved, but I do **not** self-approve novelty/significance.

The source cites Chartrand–VanderJagt–Yue, *Orientable domination in graphs*, Congr. Numer. 119 (1996), 51–63. Neither its complete theorem bodies nor the 2020 handbook were read in this fidelity assignment. No obvious public subsumption was established from the primary bodies actually read. This is not evidence that no subsumption exists. The source's general majority/ordinary-domination inequality alone does not supply the claimed improved sharp expression without further information. Existing registry-search receipts and no-solution labels are not clearance; no new literature requests, denied retries, or browser tabs were used here.

Concrete next steps belong in separate work: complete the queued independent old-theorem/subsumption and significance review, documenting exact bodies and chronology; if cleared, prepare the required paper and route final acceptance to the parent. No frozen-proof repair is requested. No paper currently exists in this candidate packet, so overall acceptance remains on hold.

## Protected inputs and limits

Exact hashes of every protected input, before and after, are in `hashes-before.json` and `hashes-after.json`; all entries match input-bindings.json and none changed. Input-bindings.json's own digest is recorded in both files and is unchanged. Key hashes:

- Majority.lean: `751ac866bed61eb765969f5ea08e53c582f79431400786e418cfd1278e07d850`
- packet zip: `5249402f7bf10a6e3176f66602a8438b2791fbfe5d080e6c3f992d73978a7ae6`
- majority.body: `1cadd079f93cca317eb5daaeb8439d4cf9c5f2571fc6d7b43bb36d718b9ec33d`
- majority.txt: `73afadfb2828da2761f7016a2d338f65220e0ab46e0f91228d411a85c9afebf5`

All writes are inside this assigned review directory. No subagents, git operations, shared edits, posting, external requests, count edits, finite orientation checker, or new paper. Read-only source inspection commands preceded the explicitly affinity-capped replay/audits; every compilation and PDF extraction was limited to two CPUs. Machine-readable verdicts and remaining gates are in `review.json`.
