# r34: collision-map weak mixing remains unresolved

Myeongjin Kang; no affiliation. CC BY 4.0. **NO NOMINEE; zero count.** The full target below is neither proved nor disproved. No independent proof or contribution verdict, acceptance, worldwide-priority claim, commit, or upload is asserted. Pinned OpenAI theorem statements and operative lemmas are stipulated true throughout.

## Target and actual progress

For every nondegenerate Euclidean triangle Q with at least one angle irrational relative to pi, prove weak mixing of the physical billiard collision map T for its probability measure cos(phi) ds dphi/(2 perimeter(Q)), on the full regular collision phase space. The initial direction is arbitrary under that measure; only the null vertex-hit and grazing trajectories are discarded. No genericity, Diophantine, symmetry, acute-angle, clearance or regular-eigenfunction restriction is permitted. This scope was identified after examining the actual source mechanism, and is retained unchanged. It is not a pre-exploration freeze.

The source proves weak mixing of the physical-time suspension flow and already derives ergodicity of T. The missing operation concerns nontrivial eigenphases of T. A collision eigenfunction is constant during flights but jumps by its eigenphase at each impact. Across a geometric seam in the oriented double, the two crossing directions consequently give opposite phases. This creates the angular multiplier exp(i alpha sign(cos theta)), which couples infinitely many modes. The source's two-endpoint Fourier-tail identity does not apply to that field.

[150-technical-lemmas.md](150-technical-lemmas.md) gives complete proofs of the following technical controls and route limitations:

- The source transverse-rigidity proposition also makes the oriented double's geodesic flow weakly mixing, by retaining two sheet amplitudes in its final reflection argument.
- The physical collision map has no eigenvalue -1: the eigenfunction times the deck sign is invariant on the double. Thus T² is ergodic. This short deduction is not offered as a substitute for weak mixing.
- The double's seam-return map (z,sigma)->(Tz,-sigma) nevertheless has eigenvalue -1, while its suspension is weakly mixing. This actual same-geometry example refutes the proposed general flow-to-return-map shortcut.
- For the general seam multiplier, a finite Hankel block has squared Hilbert--Schmidt norm (2 sin²(alpha)/pi²) log N+O_alpha(1). This is failure of finite-mode/Hilbert--Schmidt summability only; the operator norm remains bounded. It does not refute the target or all possible seam arguments.
- Removing whole seams produces the crude coefficient-energy cost O(eps^{-1}), in contrast to the source's O(1) corner cost. A higher collision-count cover does not automatically repair this: edge gluing is reversible, and a constant scalar phase would have to equal its inverse.

A successful continuation must prove a new transmission estimate or classification for bounded measurable flight-constant fields with all three direction-dependent seam phases, including grazing directions. A proof merely for the phase -1, regular fields, or a chosen triangle would change the target. No such replacement is nominated.

## History and chronology

The initial scans were too narrow to detect I52's billiard screen: searching “triangular billiard” missed a paragraph formulated as an explicit triangle. The expanded irrational-billiard/collision-map search found it before any nomination; section2B and its diagnostic discussion were then read, saved and reported to the parent. I52 screens strong mixing of one specified fully irrational acute triangle using the continuous-spectrum/Rajchman and small-divisor gaps, and develops standard-map entropy instead. It does not contain the collision-clock seam calculation. This is an earlier short family screen, not evidence of an untouched family. Eligibility would still require separate parent/contribution judgment if a full proof were ever achieved.

Earlier r34 prescreens also encountered I126's exact-length honeycomb bridge/endpoint screen, I36's technical Hilbert-valued Fourier convergence, I286's developed Cartan–Hadamard stability target, prior SK dynamics chains, family153's sextic Salem chain, and family231's technical canonical construction. They were not relabeled as new targets. Some broad search outputs were truncated; saved hit files and the reading ledger explicitly distinguish complete matched-scope reads from keyword leads. No claim to have read every campaign file or every acquired source is made.

Family237 was investigated before150: its actual mass/covering and endpoint/length-tail statements do not control the full fixed-length endpoint displacement. The source explicitly separates these statistics, and I126 already isolates joint length/spatial conditioning. No237 target was frozen. Family226's full introduction was read, but no new curve/field theorem was frozen or proved.

## Primary comparison and contribution limits

Forni–Moll's angular projection, horizontal Sobolev-domain and holonomy proofs use globally defined angular rotations and derivative domains on the regular unit tangent bundle. They do not supply the direction-dependent collision seam estimate. Chaika–Forni's final approximation argument controls finite physical-time averages and gives generic full-flow weak mixing; it does not turn physical time into collision count. Bobok–Troubetzkoy's complete final construction gives generic topological weak mixing of the map, using rational directional total transitivity and dense periodic points. Topological transitivity of a product does not settle the measure-theoretic L2 eigenfunction target. These exact operative comparisons are recorded in [reading-and-limits.md](reading-and-limits.md).

The all-polygon flow extension suggested by the source's finite-cone estimates appears source-paid and is not nominated. Nor are the parity lemma or abstract suspension bookkeeping substantial new mechanisms under this campaign's standard. The seam analysis is useful negative information about attempted routes, not a completed theorem.

## Reproduction and formal scope

Run `python diagnostic.py` for finite exact-arithmetic controls of the seam block and cutoff budgets. They are diagnostics, not proofs of billiard dynamics or of asymptotics. The analytic logarithm proof is in the lemma note.

Run `python verify.py --anchor EXTERNAL_SHA256` and `python controls.py --anchor EXTERNAL_SHA256` with the digest supplied separately by the parent. The verifier authenticates exact files and directories, rejects links and nonregular objects, and does not authorize a count. Controls mutate actual copies, including an extra empty directory, FIFO, symlink, hardlink, missing/changed/extra file, nested manifest name and root symlink.

No Lean development was started. A reasonable formal support plan, if useful later, covers the finite Hankel multiplicity identity, harmonic-sum comparison, unitary eigenspace decomposition for T² and finite sheet-sign algebra. The indispensable measurable suspension, cone-flow rigidity and general seam-domain argument would remain analytic interfaces. Formalizing the easy identities cannot certify the missing theorem.
