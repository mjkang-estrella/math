# pdtar-proof-r1: summary (MathDB 353203)

**Outcome: candidate proof closed.** The proof is ordinary and complete, it has not been self-accepted, there is no Lean certificate, and no credit is claimed. Root decides.

## Statement fidelity

**The problem.** MathDB 353203, from arXiv:2201.01798 (verbatim, raw sha256 re-verified):

> PD^TAR(K_{s,t}) is unique if and only if s ≠ 2 and t ≠ 2.

**Definitions** (verbatim from the source, written out in PROOF.md §0):

- PD sets are defined by the observation rounds P^i.
- The TAR graph has all PD sets as vertices, with an edge between two sets that differ in exactly one vertex.
- *Unique* means: for every H without isolated vertices, PD^TAR(H) ≅ PD^TAR(G) implies H ≅ G.

**The reduction.** This is the theorem of Bong, Carlson, Curtis, Haas and Hogben (Graphs Combin. 2023), restated as Theorem t:main of the survey arXiv:2406.05509v2. I read its exact hypotheses:

- the parameter must be robust, and power domination is (it is an original X-set parameter);
- both graphs must have no isolated vertices, which is exactly the uniqueness hypothesis.

Its conclusion is a vertex bijection carrying PD sets to PD sets, so equal order is part of the conclusion. It therefore applies to every admissible H, and no extra argument is needed.

**Case split** for the full "iff":

| Case | Status |
|---|---|
| s = 2 or t = 2 | Not unique. Source Corollary `mPDS:n-3:K2t`, plus the trivial K_{1,2} = P₃ versus K₃ |
| K₂ | Unique (trivial) |
| K_{1,t}, t ≥ 3 | Unique. Source Theorem `upperPDn-3` |
| K_{3,3} | Unique. Source Proposition `p:K33` |
| s, t ≥ 3, (s,t) ≠ (3,3) | **New here** |

## Prior art

No 2024–2026 resolution was found. Receipts are in `sources/web/receipts.txt` and `websearch-log.md`.

- The survey's v2 (2025-09-28) still lists the conjecture as open.
- The journal version of the source (La Matematica 5 (2026), art. 8, 2026-01-13) still states it as Conjecture 3.25. This comes from a search-engine excerpt of the publisher page.
- Direct access to the journal version was refused: Springer served a JS challenge, and the Swarthmore copy returned 403. Neither was retried. **Root should confirm this point.**
- OpenAlex shows only one citing work, the survey's journal version, and no relevant later work by Hogben.

## Proof (PROOF.md)

**Core Theorem.** Let s, t ≥ 3 with (s,t) ≠ (3,3), and let H be a graph on A ⊔ B whose PD sets are exactly those of K_{A,B}. Then H = K_{A,B}.

The proof is about two pages. Write β(a) = N(a) ∩ B and α(b) = N(b) ∩ A.

1. **Lemma 0 (fort duality).** A set S is PD if and only if every fort meets N[S].
2. **Lemmas 1–2 (blocker step).** For every fort F, N[F] contains A plus at least two vertices of B, or B plus at least two vertices of A. For each A-pair {x,y} there is a fort Ψ_{xy} with N[Ψ_{xy}] = B ∪ {x,y}, and similarly Φ_{uv} for each B-pair.
3. **Lemmas 3–5 (cross-degrees).**
   - β(a) and α(b) are never empty.
   - No vertex is a leaf hanging from the other side.
   - If |β(a)| = 1 or |α(b)| = 1, the graph must have the "hub" structure, and that structure forces s = t = 3. It is exactly the relabelled K_{3,3}.
   - Hence when (s,t) ≠ (3,3), every vertex has at least 2 neighbours on the other side.
4. **Lemma 6 (A–B complete).** Assume t ≥ 4; the case s ≥ 4 is the mirror image. Suppose a ≁ b.
   - Then the fort Φ_{bb′} contains some p ∈ A with β(p) = {b,b′}.
   - A B-pair {c,c′} disjoint from {b,b′} gives p′ ∈ A with β(p′) = {c,c′}, and both p and p′ have at least two A-neighbours.
   - The fort Ψ_{pp′} then lies inside B and contains b. So α(b) ⊆ {p}, which contradicts the cross-degree bound.
5. **Lemma 7 (r119's argument).** Once A–B is complete, both sides are independent, so H = K_{A,B}.

**Not a bridge.** The source's K_{1,t}, K_{2,t} and K_{3,3} proofs and the survey's domination proof for K_{p,q} use no forts, and none of them extends to max(s,t) ≥ 4. Details are in PROOF.md §8.

**r119's "missing lemma".** It is not proved in r119's form. The proof goes around it with the two-sided cross-degree argument.

**Abandoned route.** I also explored a one-sided "triangle lemma" route (`triangle_*.py`, `lemmaG*.py`). It needs |B| ≥ 4. It was superseded and is kept only as a record of the exploration.

## Checks (python3 -I, all capped; logs and receipts in `logs/`)

These are sanity checks only; they are not part of the proof.

- **Exhaustive lemma checks** at (3,3), (3,4) and (4,3) (`verify_lemmas.py`). Zero failures.
  - Several lemmas are tested non-vacuously, for example 912 instances of the hub-structure lemma at (3,4).
  - The (3,3) exception appears exactly as predicted: 10 relabelled copies of K_{3,3}.
- **Full enumeration at (3,4)** (`enum_groups.py`). Of all 2²¹ graphs, only K_{3,4} has its PD family.
- **Perturbation tests** (`perturb.py`), up to (6,6): no set of edge flips preserves the PD family.
- **r119 SAT logs** (copied read-only into `r119-copy/`). These are the large-scale evidence: UNSAT for every s + t ≤ 11, and for (3,8), (3,9) and (4,7).
- **Not run in this lane:** SAT solvers, Lean, lake, leanchecker.

## Lean (LEAN-PLAN.md; `lean-draft/` is uncompiled and has `sorry` skeletons only)

**Endpoint:**

```lean
TARUnique (completeBipartiteGraph (Fin s) (Fin t)) ↔ (s ≠ 2 ∧ t ≠ 2)   -- for 1 ≤ s, t
```

Here `IsPD` uses the source's round definition and `tar` is a `SimpleGraph` on `{S // IsPD G S}`.

**Estimated size:** about 2,100–3,600 lines.

- The Core part is about 400–600 lines.
- The dominant cost is Theorem R (the Bong et al. reduction), at about 800–1,500 lines. Its riskiest piece is the hypercube-interval lemma.
- K_{3,3} needs a real proof, because `native_decide` is not allowed and a kernel `decide` over all 6-vertex graphs is likely too slow.

## Residual gaps (for root)

1. There is no Lean certificate.
2. The full text of the journal version was not read directly.
3. An independent adversarial review of PROOF.md is still needed.
4. Significance and novelty need adjudication: the proof is short, but no lemma in the source or the survey covers max(s,t) ≥ 4.

## Process

- Every check ran under `scripts/limited.py`, one process at a time, with TMPDIR set to the lane-local `tmp/`.
- No background jobs remain.
- No git, no ledger edits, no uploads, no messages, no browser.
- r119 was used read-only, from copies.
