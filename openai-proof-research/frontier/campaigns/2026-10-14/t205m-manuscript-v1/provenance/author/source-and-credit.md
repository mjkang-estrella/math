# T205M source map and contribution comparison

This is an author submission for two separate independent gates. Correctness,
substantiality and worldwide novelty have not been certified. The exact frozen
all-m/all-label target is `scope205m.md`; the complete author proof is
`candidate205m.md` plus its two explicitly included lemma proofs.

## Pinned source and historical operations already paid

The source pin is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The complete
family inventory covers both *A Cyclic Polytabloid Proof of Saxl's Conjecture*
and *Universal Tensor Squares for Symmetric Groups*, dated September24,2026.
All source truths are stipulated, not audited. `source205-receipts.json`
authenticates the selected21 TeX/README blobs against that complete inventory.

| Input | Exact operation used | What is not newly claimed |
|---|---|---|
| Cyclic source `dominance.tex`, `thm:cyclic-saxl` | Every irreducible appears in the specified W_m | Ordinary Saxl positivity |
| Same, `dom:signed-average`, `dom:repeated-row-cyclic`, `dom:noncancellation`, `dom:permutation-quotient` | A sign-twisted W contains a repeated-row cyclic module mapping onto M^ρ | Sign reassociation, squared-deficit equality, noncancellation, Kostka multiplicities |
| I21 §§2.1–2.2 | The coset map is actually injective; repeated-row module is exactly M^ρ; combined signed maps are injective but individual ranks may fail | Exact dominance multiplicities or resolution of the signed conjecture |
| Cyclic source `band-quotient.tex`, `prop:band-quotient` | Full induction from the specified W_(m−1) or W_(m−2), with disjoint sectors | Generic induction, positivity, or replacing W_h by the ambient square |
| `path-band.tex`, `path:one-band`, `prop:two-band` | Trivial one-band factor; every ≤4-row constituent in the actual width-two generator | New path support or multiplicity-free two-row square |
| Companion `balance.tex` | Disjoint sector assembly, local neighboring-column squares and balanced support replacements | Replacing support substitutes by full permutation modules with their Kostka multiplicities |
| Companion `band.tex`, `capacity.tex` | Forced smaller cyclic triangle, path/attachments and first-four-capacity support exhaustion | New coordinate-sector gluing or a novel capacity-versus-balance template |
| Companion `finite.tex` | Exact character recurrences and finite support checking | New Murnaghan–Nakayama or a novel finite-verification principle |
| I17/I21 | Earlier symmetric/exterior-square full targets and their exact failures | A resolution, narrowing or rebranding of those targets |
| Accepted R026 | Integral regular summand in the staircase cube via the developed Ikenmeyer/Bryant–Kovács mechanism | A new cube result or integral refinement |

Only the four-row SUPPORT in the source is logically needed for the lower
recursion: semisimplicity supplies one copy of each constituent. The exact
U_(m,2) identification from I21 and the primary two-row square theorem is a
stronger credited fact, not a necessary hidden additional input.

## Operative primary comparisons

**Kirillov, Generalization of the Gale–Ryser theorem.** Complete ten-page
arXiv:hep-th/9304099v2 read. Theorem1.1 supplies the positive rigged-configuration
sum, Corollary1.3 the maximal configuration, and the proof of Theorem2.1 the
one-cell perturbation. These are actual operations used in the proof. The
maximal-product formula alone fails to give the desired bound on thin
rectangles. T205M chooses and estimates additional configurations uniformly
under a top-four-capacity restriction, with an explicit four-family
exception list. The perturbation itself is classical and must not be sold
as the new construction. The original Kirillov–Reshetikhin/bijection papers
cited by Kirillov were not separately read; this proof relies on the stated
published formula, not a new proof of that formula.
[Primary preprint](https://arxiv.org/abs/hep-th/9304099),
[published DOI](https://doi.org/10.1006/eujc.2000.0419).

**Vallejo, A diagrammatic approach to Kronecker squares.** Actual §8,
Theorems8.10 and8.14 and Table1 read. For each fixed tail ν⊢d, removable
skew-diagram counts and the Robinson–Taulbee formula give a piecewise
polynomial in staircase order, with degree d and leading coefficient f^ν.
This pays fixed-depth growth and near-trivial formulas. The present
quantifier permits the tail to vary with m, and its proof is an asymmetric
induction through the specified cyclic modules rather than an inference
from fixed-tail asymptotics. No new fixed-tail formula is claimed.
[Primary](https://arxiv.org/abs/1310.8362),
[published DOI](https://doi.org/10.1016/j.jcta.2014.06.002).

**Bessenrodt–Bowman–Sutton, Kronecker positivity and 2-modular representation
theory.** Actual §5, equation(5.1), Carter criterion and Theorems5.10–5.12
read. Projectivity and decomposition numbers produce quantitative lower
bounds in the stated Carter–Saxl and framed families; the classical
m−1 corner multiplicity is already explicit in the introduction. No uniform
all-label estimate for their decomposition numbers is asserted here. The
T205M operation uses source-induced quotients and configurations instead.
[Primary](https://arxiv.org/abs/1903.07717),
[published DOI](https://doi.org/10.1090/btran/70).

**Bessenrodt–Bowman, Splitting Kronecker squares, 2-decomposition numbers,
Catalan combinatorics, and the Saxl conjecture.** Published Theorem7.11
and nearby actual text read; the full odd two-row square is multiplicity-free
with precisely the ≤4-row labels. Its symmetric/exterior split is stronger
than the ordinary band support needed here. Section10's signed conjecture
is the older target, not resolved by this submission. Brown–van Willigenburg–
Zabrocki's original ordinary formula is credited through this actual primary
and the pinned companion; the original BWZ paper was not separately read.
[Published primary](https://alco.centre-mersenne.org/articles/10.5802/alco.294/).

A bounded fresh search also surfaced Soong Kyum Lee, arXiv:2512.15035v1,
*Staircase Minimality and a Proof of Saxl's Conjecture*. The author saw only
search metadata in this round. Parent reported reading the actual
Theorem1.1 positivity statement and Theorem5.3 corner formula. This is a
scope-level lead for the contribution reviewer, not an author-read body,
not a proof input, and not a certification of its modular arguments.
Parent additionally supplied Pak–Panova–Vallejo's author PDF
https://www.math.ucla.edu/~pak/papers/Saxl18.pdf as a primary lead; its body
was not read here and must not be represented as exhausted literature.

## Proposed residual contribution and its limits

The proposed residual step is the all-order sharp lower bound obtained
from a **four-exception asymmetric invariant**. It retains inherited
multiplicities in one quotient, proves two nonexceptional four-strip
predecessors at high capacity, and supplies a quantitative Kostka bound at
low capacity using the explicit configurations. A specific remaining family
has a coefficient-two LR witness. Neither transposed lower cyclic bounds
nor separate quotients are improperly summed.

The high-capacity rank-ideal construction was supplied by parent author
assistance and read in full before incorporation. Its exact bytes and hash
are in `provenance/parent-copy-receipt.json`. Parent also checked source
contracts and elementary low-capacity inequalities; none of these is an
independent gate. The active author supplied the target/invariant, low-capacity
case analysis, exceptional LR computation, full induction and finite bases.

The companion already has a capacity/balance split, I21 already has
multiplicities and arbitrary-width quotients, and Kirillov already has
positive configuration perturbations. Reviewers must decide whether the
uniform estimate and exceptional-predecessor mechanism amount to a
substantial deduction beyond these paid operations. This document does
not presume that classification. No worldwide novelty claim follows from
bounded searches or missing hits.
