# I186: reading limits and retained failed routes

2026-10-11. Original Z184 and E183 remain unresolved.
**PARK THE LOCAL-EAR MECHANISM.** Eight accepted, two remaining.
Unsealed, proof-only record.

## 1. Reading actually performed

Read in full:

* `AGENTS.md` and `sources/upstream.json`.
* `frontier/iterations/iteration186-theta-region-balance-brief.md`.
* `frontier/iterations/iteration185-connected-reconnection-brief.md`.
* `frontier/iterations/iteration184-alternating-cycle-brief.md`.
* All five I185 outputs: report, analytic attempt, reading/failures,
  input-authentication JSON, and literature receipt.
* `frontier/iterations/i185-connected-reconnection-parent-disposition.md`,
  including its finalized proof acceptance, evidence report and stopping rule.

Focused reading:

* Family 180 in `sources/CONTENTS.md`, with returned keyword-search
  context. Not the whole catalogue. The initial search also returned
  unrelated cubic/Hamiltonian entries; they were not used as sources.
* Paired-states/Barnette/Pfaffian path matches in the complete
  `sources/preprints-tree.json`. Not the full tree and not the
  truncated root-tree cache. This limited check identified the
  paired-states manuscript, not an additional relevant companion.
* Lines 55--94 and 784--838 of
  `frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`.
  These include actual `thm:main`, `cor:edge-avoidance` and
  `cor:pfaffian-paths`, both short corollary proofs, the Pfaffian
  definition and adjacent context.

No new network retrieval or remote byte comparison was made.
All pinned OpenAI results were stipulated, not truth-audited.
The full manuscript proof was not reread. External
Gorsky--Steiner--Wiederrecht statements cited by the manuscript
were not retrieved or independently invoked. There was no broad
ear-theory, companion-paper or priority survey.

The I184/I185 briefs' historical references were read as references,
not treated as a request for recursive rereading of all I183/I184
artifacts. The paid facts used here are supplied in the full I185
record, the original I184 target brief, and the finalized I185
parent response. No fresh historical proof or replay audit is claimed.

An initial instruction/path glob returned sibling-project and old
snapshot paths. Their contents were not deliberately explored;
automatically injected scoped instructions did not expand this
assignment. All intentional mathematical reading and all writes
remained within the assigned project.

## 2. Authentication chronology

Before the new proof analysis, read-only `sha256sum --check`
matched all five I185 outputs to the five anchors in the I186
brief. The same tool step recorded the SHA-256 values of that
brief and the finalized I185 parent disposition. Those observed
values are preserved in `input-authentication.json`.

The JSON receipt itself was written later with the final proof
record; it does not falsely claim to have been written before
proof work. Additional instruction/source/brief files were
hashed separately. Whole-file hashing is not whole-file reading.
No input was copied or modified, and no inherited code was run.

## 3. Written routes and their disposition

### A. Interior matching closure

**Retained deduction.** Each theta vertex already has its matching
edge on the theta. A strict-interior matching edge can neither end
on the boundary nor cross it, so each region and each connected
interior component is matched internally.

**Rejected overstatement.** The strict interior plus its entire
boundary need not be matched within that union: the matching edges
at the endpoints of $\partial\rho_{IQ}$ leave along $J$.
This is not automatically I184's forbidden shore.

### B. Cubic balance without all stubs

**Failure.** Counting only edges from the theta to interior
vertices misses boundary-to-boundary chords. Counting only a
connected interior also misses other pieces. Counting in $G'$
as if it were cubic misses terminal deficits.

**Retained correction.** In $G$, degree and matching counts give
equal theta-end black/white counts componentwise. Each boundary
chord adds one stub of each color. In $G'$ the exact equation is
$\sigma'_{\mathrm B}-\sigma'_{\mathrm W}
=d_{\mathrm B}-d_{\mathrm W}$, with boundary deficits also
subtracted from available stubs. The four terminals have two
deficits of each color, all assigned to the patch region as
interior or boundary terminals.

### C. Matching closure of a region implies opposite-colored path ends

**Failure.** A regional $H_0$ path is not alternating. Its interior
need not itself be closed under the matching, since matching
edges may join different Hamiltonian paths in the same region.

**Retained correction.** Black-black and white-white regional
paths occur in equal numbers. They need not be absent. This
distinction is essential in the length-five incidence calculation.

### D. Noncrossing paths suffice for a Hamiltonian completion

**Failure.** Separate noncrossing pairings can still yield several
cycles when combined with theta Hamiltonian edges.

**Retained correction.** Require the single circuit
$K\cup R_I\cup R_J\cup R_Q$ and coverage of every off-theta vertex
without interior cycles. The analysis explicitly traces that
circuit for the symbolic length-five data. It also retains the
two singleton endpoint paths in the common refinement, rather
than deleting their incidence information.

**Limit.** A circuit on contracted symbolic paths is not an actual
Hamiltonian graph construction. The actual paths, covering property,
interior perfect matching and all exact-instance hypotheses remain
unsupplied in that formal calculation.

### E. Complete the six-label pattern with a very short retained arc

**Exclusion proved.** Length one forces the wrong retained pair
$14$. Length three forces regional path pairs $s2,t5,36$ and
creates two monochromatic two-stub regions. This contradicts the
proved balance in cubic $G$, even allowing disconnected pieces
and chords.

**Unpaid extrapolation.** No bound forces $J$ to have length at most
three. Excluding those two lengths does not exclude the pattern,
let alone every zero-gain pattern.

### F. Extend that exclusion to all retained arcs

**Failure at the tested constraint level.** The symbolic length-five
$J=(1,s,t,w,z,4)$ admits
$K_{JQ}=\{2s,3t\}$ and $K_{IJ}=\{6w,5z\}$.
Both regions have two stubs of each color; the pairings are
simultaneously noncrossing. The Hamiltonian incidence circuit is
$1,2,s,t,3,4,5,z,w,6,1$. The retained paths recover exactly
$S=\{12,36,45\}$.

**Scope.** This only demonstrates compatibility of the written
necessary equations and the single-circuit incidence requirement.
It gives no actual graph, interior matching, patch placement,
true cut-2 identification, exterior, brace or complete fibres.
It is not a counterexample to Z184, to an exact-hypothesis
improving-ear theorem, or to the existence of a better pair at
the global minimum.

### G. Ignore the frozen patch because its color surplus is zero

**Failure.** Its six vertices are matched by $A$, but its
Hamiltonian continuations still affect regional paths and deficits.

**Retained correction.** Account for both paths
$a'-a-b-b'$ and $c'-c-x-y-d-d'$ inside the one patch region.
Their continuation terminals can lie on its boundary or inside it.
After deletion, the residual Hamiltonian object is two globally
cross-paired paths, not a 2-factor. The zero-stub third region
of the symbolic data could not contain the patch in a realization.
No accommodation of the patch in the other regions is asserted.

### H. Reuse I184 reachability to force improvement

**Failure.** Region matching closure and color balance give
potentially many boundary edges, not a sole-exit reachability
shore. Absence of a component-reducing ear is still not absence
of ordinary directed paths. Component-filtered search projections
need not preserve matching closure or outgoing-neighbor closure.

The reviewed I184 lemma is not weakened or reopened, and no
residual two-extendability assertion is made.

### I. Let the secondary minimum or other completions pay the gap

**Failure.** Equal component count and $|I|=|Q|$ do not improve the
lexicographic objective. No plateau-escape theorem is proved.
The symbolic pattern is not shown to occur at any global minimum.

The minimization is over all completions, not an arbitrarily fixed
one. During each proposed splice its selected completion stays
fixed. Failure of a local deduction for one completion cannot
refute the original existential target.

### J. Use complete fibres, fixed exterior, or a stronger upstream theorem

**Unpaid.** The exact exterior and complete fibres are retained,
not replaced by arbitrary attachments or representatives.
Their available information has not been connected to the
simultaneous regional Hamiltonian path orders needed here.
Brace extension of matching edges is not a path-order theorem.

The actual upstream statements give Hamiltonicity, one-edge
avoidance, and one prescribed three-edge path under their own
hypotheses. None is a frozen-matching, single-ear connected-toggle
theorem. No external theorem is silently strengthened or invoked
unread.

## 4. Stopping decision and preserved history

**Park the local-ear mechanism.** The new bookkeeping and short-arc
exclusion do not produce a usable universal improvement bridge.
Missing information concerns actual matching/Hamiltonian path
orders, available eligible ears and their relation to complete
completion/fibre choices and the fixed interface. Another name
for the same unpaid pairing inequality is not a new research task.
No next broader program step was begun.

Parking is neither refutation nor resolution of Z184/E183.
Z184 implies E183; neither converse nor strict separation is
proved. E182/E181/H180/L179, universal exchange, (T) and Q164
remain open. The accepted count is unchanged.

The old formal pairing objections remain formal, not graph
counterexamples. Earlier multiple-toggle, fixed-exterior rerouting,
automatic frozen-matching descent, D168/M168 transfer/fullness,
deleted-coordinate, failed-containment and isolated-toggle
shortcuts are not revived. Historical provider failures or
incomplete checkpoints are not erased by later parent checks.

## 5. Validation and operational boundary

Internal written validation checked matching saturation, all three
region balances, each disconnected piece, chord counting,
same-colored path cancellation, all four deficits and their signs,
patch paths, short-$J$ exclusions, the explicit Hamiltonian
incidence circuit, and both old/new retained-path traces.
Document validation checks only the five output files, JSON
syntax, local links, consistency and input hashes.

No graph generation/construction/tests, numerical experiments,
attachments, sweeps, matching scans, research implementation,
historical replay, snapshots, seal framework, agents, shared-ledger
or ancestor edits, staging, commits or publication occurred.

The finalized parent's inherited 23-stage I183 replay in about
8.70 seconds, eight probes and source positive control is reported,
not rerun. Twelve facial and 626 matching controls stay finite.
There was no independent reviewer, proof assistant or contribution
clearance in this round. Any substantial candidate must pass those
separate gates.
