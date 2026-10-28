# Astra discrete research, round 2

Solo research; no child agents, shared edits, git, or public mutations.
Assigned lane: `astra-discrete-r2`. No acceptance or counting authority.

## Initial state (2026-10-28 UTC)

Read ancestor and batch AGENTS.md, batch ledger and prior-campaign context,
cancelled `pi-discrete-r1/progress.md`, earlier `pi-discrete-discovery-r7`
findings/progress/discovery/provenance, and root stop list. First 30 outcomes
are excluded. Ledger records zero accepted additional outcomes.

Primary attack: BBK Conjecture 5.1, exact positivity of
`G_{k,n}=(q^(2k-1);q^2)_n/(q;q^2)_(n+1)` for k>=1,n>=0.
The earlier lane has not proved uniform positivity. Its saved numerical
claims and simple-pole argument will be treated as evidence to check, not
as an accepted theorem. Chern–Wang's full m=1 result does not automatically
prove this coefficientwise refinement.

Next: refresh source/companion provenance; seek a uniform algebraic or
combinatorial proof, retaining exact experiments and documenting failures.

## First attack checkpoint

- Live primary BBK HTML and Chern–Wang HTML saved and hashed, alongside the
  three previously abstract-only companions 2604.05403, 2606.30208, 2609.05961.
  Keith's Alladi70 talk abstract independently describes the refinement after
  the original positivity proof; direct fetch returned 406 (web search read).
- Exact monotonicity difference identity derived. `checks/monotonic_scan.py`
  checked 1,665 pairs n=1..30, n+2<=k<=2n+41 through degree
  2n+1+4n(k+n), using integer arithmetic. No negative coefficient found.
  This is explicitly finite evidence, not an all-coefficient result.
- Generic weighted-complete-intersection proof fails already at n=4,k=6:
  weights 1,3,5,7,9; relation degrees 11,13,15,17. Setting the first three
  variables to zero annihilates all relations, leaving dimension at least 2.
  Thus the intended one-dimensional quotient cannot be such a complete intersection.
- Companion 2606.30208's unbounded-sign conjecture is already addressed by
  Dhar–Goswami–Tripathi 2607.10576. Its parity conjecture is on the root stop list.
- Brief power-sum lead 1110.6813 Conj4.8 has a scaling defect, but a result based
  only on missing gcd normalization is ineligible under the task; not pursued.
- Considering a genuinely different discrete target, the full integer-q
  Sturm property of Hoggatt sums (MathDB368343), subject to source/prior-art gate.

## Hoggatt proof checkpoint and handoff

A complete written argument now appears in PROOF.md for real q>1 and every
m>=2; with the known q=1 theorem it implies FZZ Conjecture 4.1, including
all n>=1 and both requested levels m=2,3. The key invariant is strict
multiplicative q-separation after ordinary Hadamard multiplication, followed
by a q-Markov argument with nonnegative partial-fraction residues.

Exact rational checks passed: 288 coefficient-identity cases and 1,296
MacMahon-normalization cases. They are corroboration only. The three small
Lean algebra/order bridges compile using pinned Lean and only standard3
axioms. BRIDGES.md lists all missing formal obligations; the full theorem is
NOT a checked endpoint.

Read actual bodies of Garloff–Wagner Theorem 4 (indexed original page 800 and
FZZ's full restatement), FZZ's q=1 proof, Dilks Theorem 3.8, Lamprecht
Theorems 25/29/30, Leake–Ryder Proposition 3.6, and 2026 q-convolution,
Hoggatt-triangle and strong-q-log-convexity papers. The latter cover different
properties. MathDB's two extra companion links are false matches: one is
about generic split polynomials, the other concerns a distinct Narayana
refinement whose conjectures are already resolved. No credit is inferred
from empty registry solution arrays.

Strongest objection: the new proof adapts FZZ's published q=1 induction using
classical q-separation machinery. Root must evaluate nonroutine eligibility
and subsumption independently. No acceptance/counting or shared-file edits.
BBK refinement remains unsolved here.
