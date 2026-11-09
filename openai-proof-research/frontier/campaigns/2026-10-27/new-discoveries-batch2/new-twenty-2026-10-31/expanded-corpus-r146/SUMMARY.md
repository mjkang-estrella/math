# expanded-corpus-r146 (Claude, reserve7): summary

Lane: `new-twenty-2026-10-31/expanded-corpus-r146`, 2026-11-04 UTC. Investigator only. No child agents,
no git, no ledger edits. Lean, lake, SAT/ILP solvers and compiled helpers were not run. Zero credit
unless root accepts; nothing here is self-accepted.

## Outcome

**One candidate: 337352** (Cheon–Jung–Kitaev–Mojallal, *Riordan graphs I*, Conjecture 2).

* **Theorem.** For every k ≥ 4, an io-decomposable Riordan graph of the Bell type on 2^k vertices with
  diameter k has an all-ones binary A-prefix, so it is the Catalan graph CG_{2^k}.
* **Consequences.** Conjecture 2 holds in the family reading. The per-k reading holds exactly for k = 1
  and k ≥ 4, and fails exactly at k = 2 and k = 3. The k = 3 exception, 1111110 (CG_8 plus the edge
  {1, 8}), is already printed in Jung's Table 1, so a literal per-k refutation earns nothing.
* **New ingredients.**
  * Lemma A: by Lagrange inversion mod 2, the last vertex N = 2^K is adjacent to j iff j is odd and
    [w^{N−1−j}] A^{−1} = 1.
  * Lemma B: the first zero at index p in [2^{K−1}, 2^K − 2] forces the edge {N, N−1−p} into the low
    half.
  * Lemma C: combined with the published fractal, universal-vertex and Catalan-distance lemmas, the
    diameter drops to ≤ K − 1.
  * Induction from an exhaustive k = 4 base.
* **Prior partial result.** Jung (Graphs Combin. 38 (2022) 7, arXiv:1901.11156) proved the uniqueness
  only when the A-sequence differs from all-ones within its first 16 entries. That proof relied on
  computer tables.
* **Evidence.** All io sequences checked exhaustively for k = 2, …, 5. For k = 6, all 65,536 sequences
  the induction leaves open were checked; only the all-ones sequence has diameter 6. Lemma A was
  checked on 800 random Bell-type A-sequences, and Lemma B on all restricted K = 4–6 sequences plus
  3,000 random K = 7 samples. Code: `scripts/riordan*.py`; logs and receipts in `logs/`.
* **Deliverables.** `outputs/337352-proof.md` (complete ordinary proof, readings, novelty and credit
  assessment, Lean plan) and `lean/Riordan337352.lean` (UNCOMPILED draft: source-literal definitions,
  endpoint statements, induction skeleton, with `sorry` marking open obligations).
* **Lean cost: HIGH.** The general-k structural lemmas and Lagrange inversion mod 2 must be
  formalized. There is no finite-certificate shortcut.
* **Family warning.** The credited 338258 comes from *Riordan graphs II*: a spectral odd-kernel
  conjecture, a different invariant with a different mechanism. 337352 is not a parameter variant of
  it, but it is the same object family. Root should weigh the concentration and bridge-risk concerns
  (see `outputs/337352-proof.md` §5).

## The 20 dispositions (details in results.json)

| ID | Outcome |
|---|---|
| 337352 | CANDIDATE (see above) |
| 330508 | Dehmer–Kraus Conj. 4.2 is trivially false at n = 5: with c = (1/2, 1/3, 1/4), I(P_5) = log₂5 > I(S_5). It follows from the source's own Lemma 4.1. Zero credit. |
| 330518 | Proved in the source (Gregor–Lužar–Soták). |
| 332393 | The literal "countably infinite graph" wording is trivially false. The intended Milićević conjecture is proved for r ≤ 5 (Pokrovskiy 2025) and open in general. |
| 332603 | Infinite-graph tree decomposition conjecture; open; parked. |
| 332860 | Refuted in the literature (bow-tie graph, Sedlar–Škrekovski). |
| 333133 | Zhu's (5m−1, m)-choosability conjecture; open; parked. |
| 333742 | Cyclic-group Fuglede conjecture (Dyatlov–Jin Conj. 3.15); open and famous; parked. |
| 333826 | Merker–Postle bounded diameter arboricity conjecture; open; parked. |
| 334118, 334119 | Source-fidelity defect: no G-positivity poset conjecture appears in arXiv:1609.06171 (v1 is the only version) or in its Involve version. |
| 334560 | Refuted through the source's own special case, Conj. 1.11 (Stein's conjecture), by Pokrovskiy–Sudakov (PAMS 2019). |
| 334570 | Proved (arXiv:1806.03774); also a routine classical bridge. |
| 334722 | Brown–Erey 2-connected ear conjecture; open. Partial results: Engbers–Erey–Fox–He (x = k) and Yang 2023. Parked. |
| 334795 | Refuted for disks (Damásdi–Pálvölgyi). |
| 334947 | Secant degeneracy refinement; algebro-geometric; parked. |
| 334964 | Akbari–Alipour unbounded-gap conjecture; open. The Z_2^k sum invariant caps that family at gap 2. Parked. |
| 337294 | BGS pairing conjecture; open, verified n ≤ 5. An n = 6 check is beyond capped python. Parked. |
| 337528 | Proved (Bürger–Pitz, arXiv:1711.08711). |
| 337577 | Resolved (Li–Su–Fallat, arXiv:2306.16247), including a counterexample to the "in particular" clause for disconnected subgraphs of 3-trees. |

## Checks performed

* **History.** Exact-ID search over campaign `*.md/*.json/*.txt` (`logs/history-grep-files.txt`,
  `logs/history_context.log`). It found only sitemap, routing and coverage lists, coincidental number
  strings, and the r146 launch note in `ledger.json`. No prior exclusion exists for any reserved ID.
* **Current versions.** arXiv abstract pages were read for all 20 sources, and the version history was
  checked:
  * 1710.04604: v1 and v2 both pose Conjecture 2.
  * 1609.06171: v1 only.
* **Registries.**
  * OpenAI/math HEAD is 4eaee875 (unchanged).
  * Omega HEAD is now 09d497c2, which differs from root's last record. I fetched complete D5 (13,881
    entries) and Problems (1,714) trees, both untruncated, and ran a path screen
    (`outputs/omega-tree-screen.json`). No hit relates to these items. This is a path screen only,
    not body reading.
* **Network.** TLS verification was left on. No retries of denied routes. One expected 404 (an FAU PDF
  link). Springer served the published abstract page.
* **Resources.** One python3 process at a time, all under `scripts/limited.py` (2 CPUs affinity,
  CPU 120 s, wall 140 s, RSS kill at 1.5 GiB, AS 4 GiB, MALLOC_ARENA_MAX=2).
  * One history-context run hit the RSS cap and was rerun in streaming form.
  * An early unwrapped `grep -r` over the campaign tree exceeded the 120 s foreground limit, was moved
    to the background, and was stopped by me; it wrote no lane files. The harness kept its output
    file in its own task directory under /tmp; I did not write it.
  * No background job is left running.

## Remaining precise lemmas for 337352 (formal stage)

1. Generating-function bridge: b_{i,j} = [z^{i−j}] g^{j+1}, with g = A(zg) over ZMod 2.
2. Lagrange inversion mod 2 for odd n = 2^K − 1 (Lemma A).
3. General-k formal proofs of (P1) universal vertex, (P2) fractal self-similarity, (P3) distance
   structure of CG_{2^s}, (P4) diam ≤ ⌊log₂ n⌋ and (P5) the doubling bound.
4. The k = 4 base case by kernel `decide`, using a proved-sound checker.
5. Lemmas B and C and the induction (sketched in the Lean draft).
