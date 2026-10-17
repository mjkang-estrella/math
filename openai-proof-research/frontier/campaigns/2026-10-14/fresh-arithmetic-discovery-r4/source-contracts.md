# Source contracts and eligibility limits

Status: complete author-level proof attempt of the unchanged full S2 target;
independent proof and contribution decisions pending. No campaign count awarded.

## Stipulated source and complete family

Pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, family 173,
*A proof of Seymour's second-neighborhood conjecture*, 23 September 2026.
The complete nontruncated `sources/preprints-tree.json` inventory has 13,223
entries. Its family subtree has one manuscript, all six substantive sections,
main file, one TikZ figure, bibliography, README and the compiled paper PDF;
there is no separately advertised companion in that subtree. All source TeX,
bibliography and README are preserved in `inputs/seymour/`; original paths,
pinned raw URLs, Git blob identities and SHA256 values are in
`inputs/source-manifest.json`. Downloaded blobs were matched against the tree.
The compiled PDF is an alternative rendering, not a separately used premise.

Read fully: 00-introduction, 01-reduction, 02-pruning, 03-incompatibility,
04-weighted-consequences, 05-directed-cycle-consequences, main, README and
references.bib. The TikZ figure was preserved but not semantically inspected.

Imported theorem: every nonempty finite oriented graph has a vertex whose
exact second out-neighborhood has cardinality at least its out-neighborhood.
Imported lemma: `lemma:pruning` in 02-pruning, for any finite binary relation,
retains conflict-free initial members and produces compatible subsets with
deletions bounded by the initial conflict-charge set plus the eventual
uncovered set. Candidate Section 6 specifies the charge set, diagonal
retention, and both bounds in its application. These source results are
stipulated; this task does not claim to independently establish them.
The source subset-pruning reduction, transitive blowup count and extremal
compatible-pair closure are explicit antecedents, not newly claimed operations.

## Closest external primary body

Suresh Dara, Mathew C. Francis, Dalu Jacob, N. Narayanan, *Extending some
results on the second neighborhood conjecture*, Discrete Applied Mathematics
311 (2022), 1–17, DOI 10.1016/j.dam.2021.12.034.
Actual primary preprint: https://arxiv.org/pdf/1808.02247v3, preserved as
`inputs/dara-1808.02247v3.pdf` and extracted `inputs/dara.txt`.
Read extent: substantive pages 15–21, extracted lines 790–1142, including
Theorem 6, Lemmas 18–25, Corollary 5, and concluding Conjectures 2–3 and
Proposition 8. Earlier dependency proofs were not all read; none is imported
as a premise. Conjecture 2 is precisely our target, and Conjecture 3 is its
unique-good/sink formulation. Theorem 6 establishes deletion survival when
the deleted graph is a tournament missing a matching. Its safe completions,
periodic median orders, module partitions and auxiliary acyclicity are
antecedents. The candidate gives no priority claim for the conjecture or for
these restricted results.

The proposed unpaid operation is retaining the exceptional successor boundary
after deleting the sole good vertex, then obtaining strict TOTAL compatible
fiber inequalities from m−1 anchors in just one transitive blowup block.
The gain m(m−1) exceeds the n²m residual bound with m=n²+2. The argument does
not claim every blown-up subset has negative deficit. Source Section 01's
all-vertices-bad assumption is replaced by the explicitly proved protected
exception argument in candidate Sections 1–3; it is not silently reused.
Whether this adaptation and aggregate gain constitute a sufficiently new
contribution is left to the separate gate.

## Eligibility and bounded-search limitations

The latest NEW-TEN and earlier TEN/TWENTY/iteration records and original
complex-projector-borsuk-parent/fresh-r17-brief were consulted for exclusions.
The full catalog title scan and selected descriptions covered 372 families
and 719 advertised manuscripts; this is not a claim to read every manuscript.
Families 198 and 174 were screened without freezing or nominating a result.
For 198 only introduction and selection-process bodies were read fully;
for 174 introduction and sparsification were read fully. Their other
preserved downloads are not represented as semantic reading. Family 024's
unresolved totient target remains unchanged and is not recycled here.

Parent identified prior Seymour fallback mentions in I161/I164. Actual
I164 development concerned Barnette Hamiltonian multiplicity. Consequently
this packet claims no prior absence of the family name: the bounded history
check found fallback mentions, not an earlier developed S2 proof. Parent
must confirm eligibility against its full ledger. Existing exclusions and
accepted families are not displaced by this nomination.

A bounded web check found restricted two-vertex antecedents and a recent
Tahara excess-bounds repository; its search snippet was not a primary-body
comparison and supplies no novelty conclusion. No exhaustive literature
absence claim is made. Independent contribution review should check current
bodies as well as the pinned source and Dara paper.

## Diagnostics

`python verify_math.py` checks 352,224 exact boundary identities over 23,664
small oriented graphs, and a six-vertex counterexample to the tempting
but false shortcut that strong connectivity and weak subset deficits force
all singleton deficits to vanish. Output is `math-checks.json`.
Finite checks do not prove S2; the claimed universal proof is candidate
Sections 1–6. No Lean proof, manuscript acceptance, or publication is claimed.
Historical checkpoint files retain earlier unresolved stages; candidate.md
supersedes those stages without narrowing scope.md.
