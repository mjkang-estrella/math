# Expanded corpus r97 — partial research handback, zero accepted credit

The strongest output is a full ordinary proof candidate for **371637**, the odd-wheel Cartesian-square fractional chromatic formula. See [outputs/WHEEL-PROOF.md](outputs/WHEEL-PROOF.md). Its missing uniform step is a simultaneous deletion in both rim coordinates: the surviving graph splits into rectangular grids, and the odd component counts give the required weighted independent-set bound. An explicit orbit-averaged fractional coloring attains it. The source's active profiles and linear system are credited, not claimed new. The manuscript and companion code do not state the added argument in the portions read.

**This is not an accepted solution or a complete fulfillment of the requested assignment.** There is no literal Lean endpoint. The graph decomposition, grid matching, independent-set constructions and fractional-cover averaging remain to be formalized; no arithmetic surrogate is supplied. Wider prior art and significance remain unreviewed. In particular, the root might judge the ordinary argument an elementary bridge from source ingredients. No novelty or eligibility PASS is claimed. No Lean packet has been fabricated.

The exact 20 reserved IDs have entries in [results.json](results.json), each with its literal statement, source and raw provenance, review depth, mathematical attempt, actual coverage, remaining gap and zero credit. Raw corpus lines including their newline are in `raw/`; `extracted.json` includes one-based chunk locations and chunk/raw/statement hashes. Source bodies, dated URL/status/hash receipts, scripts, full logs and numerical outputs are retained.

## Scientific dispositions

- **371637:** ordinary full-scope proof candidate, unformalized and unreviewed. Independent weighted MIS diagnostics ran for t=2..12; only t<=6 reached solver optimality. Every pair of nonempty independent rim sets in C5,C7,C9 (6,509 pairs) passed an independent bipartite-matching comparison. Closed profile/cover coefficients were checked through t=40.
- **363149:** already resolved in the current public Omega registry. The pinned `CycleStarIrregularity` source and problem note were fetched and read, including the unbounded labeling, lower bound and literal two-range leastness theorem. No rediscovery credit.
- **362719:** excluded as a routine parity consequence. Every printed map changes letter parity by a constant; equal VT sum residues give equal image-weight parity, and deletion overlap bounds the difference by one. Full argument in `outputs/VT-PARITY.md`.
- **371150:** strengthened Euler checks to exact mod-2 homology of Alexander duals. In addition to 61 bounded Euler cases and 13 small homology cases, the sparse search checked k=3 at (n,p)=(34,3),(40,3),(48,3),(34,4),(40,4), beyond the source's largest reported k=3 value n=33. No homological obstruction appeared. Homology agreement does not prove a sphere homotopy type.
- **371155:** 189,550 sumset tests across (h,k)=(4,8),(5,7),(5,8),(6,7). Every predicted size has an explicit witness in the first two pairs, beyond the source h+k<12 range. Finite-search gaps for the other two pairs are not impossibility results or counterexamples.
- **372013:** 20,350 exact small weighted-tournament/split tests, plus 3,000 seeded weighted kernels with all splits at selected lengths through64 and seven nonlinear optimization searches. No violating kernel found. The source's six-edge counterexample has three flips, so it does not refute the one-flip conjecture.
- **364207:** 343 Sylvester row-deletion cases, with exhaustive remaining cube vectors. Small nonmaximal examples exist, but the conjecture is eventual in matrix order for each fixed deletion count; these examples are not refutations.
- **372236:** 34 flow DAGs and 156 framings, with actual route coherence, maximal cliques, rotations and all intervals tested. Counts agree in every tested case. This is a small diagnostic range; the source gives no numerical verified cutoff to surpass.
- **363221:** exact F2 separator-rank diagnostics for cycles C6..C9 and the level2 binary tree; full degree ranges in results.json. No contrary case. This is a binomial-prime calculation, not the monomial edge-ideal invariant.
- **361614:** bounded successor graph searches, all starts1..250000 for each base3..16, with termination and boundary escapes separated.
- **362849:** exact coefficient-parity searches through50000 for t=29,33,...,257. Every residue class modulo every A<=128 contains an odd coefficient in the checked range. This neither proves density nor rules out all arithmetic progressions.
- **371638:** capped triangle-product MIS attempts at ell2, t3,4,8,9; unresolved solver gaps. The ell1 source consequence is an excluded parameter instance.
- **365063:** original r130 unresolved report read; route not repeated. **361402** and **365185:** source-backed complexity/analytic dispositions only.

Five finite targets have source review but **no new invariant computation**: 363624 (partition discrepancies), 372351 (hook Gram determinants), 382363 (actual coinvariant quotient multiplicity), 382392 (Speyer polynomial), 382454 (nonuniform finite-chain stationary law). These are explicit unmet search requirements, not negative results. The dossier must not be described as a complete expanded-corpus deep pass or a several-hour completed campaign. Their exact semantic/algorithmic gaps are recorded individually. No target is promoted merely from computational agreement or an open label.

## Source, history and registry limits

All19 distinct primary arXiv HTML bodies were retrieved successfully; all20 literal MathDB statements were read from the immutable local corpus. The entries specify selected statement/definition/proof depth; full-paper review is not claimed for every source. No MathDB live access or exhaustive citation survey is claimed.

The bounded historical ID/title screen is in `history-matches.txt`. Its main substantive overlap was the original Ulam report `sol-fresh-source-discovery-r130/discovery.md`, which was read and preserved as unresolved. Most other hits were assignment metadata or incidental long numerical/registry strings. `outputs/inherited-context.json` records read-only ledger hashes and accepted/excluded families. The protected rigid-cube result and adjacent Kadar–Yu formalization were not taken over.

Live registry receipts used **/commits/HEAD only**:

- OpenAI/math: `4eaee87548250b2682affda7d05d947c05554bae`, unchanged; byte-hashed cached complete preprints listing reused.
- Omega: `9e88f6fbe4681a1f5617c2673e72e9d814178a53`; fresh complete, nontruncated D5 and Problems trees fetched.

Path-screen scope and hashes are in `outputs/registry-screen.json`. Only the cycle-star matching proof body was read for an exclusion; absence of another filename is not a novelty certificate. The wheel authors' companion repository was fetched at its own HEAD and its README/profile code read; it uses binary MILP enumeration and reduced LP. No denied route was retried, and no browser tabs, external messages, uploads or publication occurred.

## Reproduction and resource records

Run scripts from this lane with `python scripts/limited.py NAME python scripts/SCRIPT.py`. Every significant numerical/fetch process was run with two-CPU affinity, CPU120s/wall140s limits and a sampled6GiB RSS guard. Logs retain each command's exit status, wall time and sampled RSS. Monitoring is not a cgroup-level or transient-memory guarantee. `wheels.py` supplies additional per-solve time limits; its numerical bounds are diagnostics, not kernel certificates. Initial unavailable-g++ compilation and an initial Hadamard JSON serialization failure are preserved; the successful NumPy and corrected Hadamard runs supersede them. No dependencies or shared files were changed.

The final validation checks exactly20 reserved ID keys, preserved raw bytes and hashes, source receipt hashes and result schema. No Lean build, leanchecker run, axiom audit or upstream-cache rebuild is claimed. All launched execution sessions have completed; no background jobs remain. Root acceptance remains separate and credit is zero.
