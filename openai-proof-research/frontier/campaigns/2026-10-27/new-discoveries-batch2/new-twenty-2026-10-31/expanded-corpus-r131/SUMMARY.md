# expanded-corpus-r131: summary (Claude Opus 5.5 investigator, 2026-11-03)

Twenty reserved IDs (reserve5). Exactly 20 ID-keyed entries are in `results.json`. Nothing is
self-accepted; zero credit unless root accepts. No Lean, lake, leanchecker or SAT/ILP binaries
were run. Pure `python3 -I` ran one process at a time under `scripts/limited.py`, with receipts
in `logs/`.

## Headline: one full-scope candidate

**343536: Neuberger–Sieben–Swift Conjecture 5.6 (equitable partitions of P_m □ P_n).** I have a
complete ordinary proof for all m, n ≥ 1 of all three sentences (`PROOF-343536.md`):

1. Every equitable partition π is the orbit partition of H(π) = {g ∈ A0 : χ∘g = χ}, where A0 is
   the explicit reflection group (Z2×Z2, or D4 when m = n).
2. Aut(P_m □ P_n) = A0 whenever some vertex has trivial A0-stabilizer. Such a vertex exists
   exactly when not 2 ≤ m = n ≤ 3.
3. The lattice of equitable partitions is isomorphic to the subgroup lattice exactly in those
   cases. In the 2×2 and 3×3 cases, the rotation subgroup and A0 have the same orbits, so the
   two lattices are not even equinumerous.

How the proof works:

* Cells respect degree and boundary layers.
* Row determinism: one full side of colours fixes the rest.
* Border transitivity, using side walks with corner timing.
* Inward propagation, using a unique outward-neighbour property.
* Separate path and ladder cases, and transposition for n ≤ 2.

Exhaustive diagnostic cross-check (`scripts/grid_equitable.py`, logs `grid-eq-*`): equitable
partitions equal the orbit partitions for 1×n and 2×n (n ≤ 20), 3×n (n ≤ 13), 4×n (n ≤ 10),
and 5×5 through 5×8. Trivial stabilizers are absent exactly at 2×2 and 3×3.

The source verified by computer up to 20×20 and gives no proof. Prior art searched:

* both arXiv versions;
* the authors' 2024 follow-up arXiv:2411.10904 (v1, v2);
* their companion site;
* web searches on grid equitable/orbit partitions and on balanced colourings in coupled-cell
  networks (Wang–Golubitsky and Dias–Pinho treat infinite or periodic lattices);
* registry trees: Omega HEAD 5aef460c (D5 and Problems complete, untruncated) and the OpenAI
  preprints tree at HEAD 4eaee875.

No proof was found. A journal version of the source was not located.

Lean: `lean-draft-UNCOMPILED/Grid343536.lean` (statements for all three sentences, explicit
automorphisms, skeleton lemmas, `sorry` placeholders) and `PLAN-343536.md`, with the
correspondence and an estimate of about 1500–3000 lines. These are not compiled and not a
certificate.

Reviewer cautions: the proof is elementary and self-contained, about two pages. The source
contains no grid lemmas to bridge from. Path and ladder cases are classical in flavour.
Significance and novelty are root's call.

## Sustained searches beyond source ranges (no counterexample)

* **339049, Linusson–Potka Conjecture 4.3** (EG⁻¹(Q) maximal and ℓ_Q = Σ(EG⁻¹(Q)_i − c(Q)_i)).
  Exact definitions are implemented (EG insertion Def. 2.1, frozen tableaux, inverse by
  promotion Thm 2.5, prefix-constrained enumeration of W_Q). The implementation reproduces
  Table 1 exactly for n = 3, 4, 5.
  * n = 6 is exhaustive: all 292,864 SYT(sc_6), with 0 failures and max |W_Q| = 5880 (shards in
    `outputs/egf-6-shard{0,1,2}.json`).
  * n = 7: 3,455 uniform hook-walk samples, 0 failures, max |W_Q| = 82,880.
  * Resource note: the first n = 7 run peaked at 2.76 GB RSS, over this lane's under-2 GiB rule
    (it was within the 6 GiB wrapper cap). The second run was memory-capped and peaked at 224 MB.
* **369840, Deb Conjecture A.3** (coefficientwise Hankel-TP of P_n(x+1) for vincular classes 1
  and 2; the source verified the 10×10 submatrix). The rank-of-last DP is brute-force checked
  for n ≤ 8 and computed to n = 34. Exact Kronecker-substitution minors give:
  * all contiguous minors positive: class 2 to index 24 (complete); class 1 complete through
    11×11 before the CPU cap;
  * all minors of size ≤ 2 of the leading 14×14 positive (both classes);
  * all minors of the leading 8×8 positive.
  Sanity check: the unshifted class 2 fails at a 3×3 minor, consistent with the source.

## Exclusions (zero credit)

* 339076: public Omega refutation (`oh-scrimshaw-2018-two-shifted-q-motzkin-hankel-refutation`),
  plus earlier campaign q-Motzkin lanes.
* 340156: Hibi–Matsuda deleted the conjecture in v2; a counterexample is in arXiv:1906.05510.
* 344161: the source v4 cites Mejía Gómez's resolution.
* 366032: source v3 Remark 6.5 records a proof of Conj. 6.4, which implies Conj. 6.1 by Thm 6.6(a).
* 338263: source v3 Remark 4.6 says the result was proved by Eid.
* 339553: Saltz proves parts 1–3; part 4 is parked.
* 341256: the authors checked every response-matrix entry but one. That entry follows from
  Kirchhoff zero row sums, so the conjecture is a bridge from the source's own computation plus
  a classical fact.

## Parked

* 341292: the source's Prop. 10.13 refutes the universal form under a rank-into-rank cardinal;
  n = 6 needs A_64.
* 352683: Keller's question; the source searched n ≤ 15. An Alkauskas 2026 follow-up is partial.
* 344963: the constraint text layer is garbled; a small-T exact LP vertex search remains possible.
* 338974: needs a small-type root-system search.
* 338731, 339832, 343979, 344785, 364816, 373759: hard, analytic or asymptotic.

## Receipts and access

* arXiv abstract pages for all 20 sources, and PDFs for the read sources, in `sources/` with
  receipts. Version histories are in `outputs/arxiv-versions.json`.
* Registry HEADs via GitHub `/commits/HEAD`: OpenAI 4eaee87548250b2682affda7d05d947c05554bae
  (unchanged); Omega 5aef460c4002fb56128a014759b022a775674653 (new since the root's
  b576c901, committed 2026-11-03T12:06Z). Trees and the keyword screen are in
  `outputs/registry-screen.json`.
* There were no 403 or 429 responses.
* The history grep over the 2026-10-25/26/27 campaigns is in `outputs/history-grep.txt`. Only
  339076 had prior substantive work; the other hits are inventory listings or numeric
  coincidences.
* Raw corpus lines are in `raw/<id>.jsonl`, with chunk, line, raw and statement hashes in
  `extracted.json` and `results.json`.

## Web searches used (2026-11-03)

* Piercing-chessboard follow-ups.
* Grid equitable/orbit partitions (two queries).
* The resistor hexagon move.
* Edelman–Greene P_Q conjecture status.
* Neuberger–Sieben–Swift follow-ups.
* Balanced colourings of finite grids.

Sources noted: arxiv.org/abs/2111.09702, web.vu.lt/mif/g.alkauskas/math/piercing.pdf,
arxiv.org/abs/1908.05797, arxiv.org/abs/2411.10904, jan.ucc.nau.edu/ns46/invariant,
arxiv.org/abs/1812.01517, arxiv.org/abs/1804.10034,
mat.univie.ac.at/~slc/wpapers/FPSAC2018/79-Linusson-Potka.pdf, and
cmup.fc.up.pt/main/sites/default/files/publications/DiasPinho.pdf.
