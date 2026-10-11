# I184 reading, failed routes and limits

2026-10-11. Proof-only round. Z184 and E183 remain unresolved.

## Reading actually performed

* Read `AGENTS.md` and `sources/upstream.json`.
* Inspected the actual family-180 entry in `sources/CONTENTS.md`
  and its complete manuscript-path entries in
  `sources/preprints-tree.json`. Did not read the entire catalogue
  or the unrelated manuscript listings. Did not use the truncated
  root-tree cache as a manuscript inventory.
* Read the full I184 brief, full I183 final analytic review, full
  I183 final report, and full finalized I183 parent disposition.
* Read the resumed analytical attempt, including all of Sections
  1--6 and the short Section 7. Its incomplete computational status
  is historical, not the status of the later finalization.
* Read the finalization literature receipt to locate the actual
  retained upstream source.
* Read the actual statements `thm:main`, `cor:edge-avoidance` and
  `cor:pfaffian-paths` in
  `frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`.
  Read the two short corollary proofs and the nearby Pfaffian definition.
  Search context also displayed nearby introductory text and the end
  of the main proof. This was not a full manuscript proof reread.
* The catalogue/path check identified the paired-states manuscript
  for family 180, not an additional simultaneous-prescription
  companion. No external companion-paper or priority survey was
  performed. The external Gorsky--Steiner--Wiederrecht proof was
  not read or independently invoked.

No network retrieval was needed. The source receipt gives the pinned
raw URL, local source path, statement labels, hashes and reading limits.
All pinned OpenAI results remain stipulated true.

## Authentication and operational scope

Before proof work, SHA-256 was computed for the final I183 report,
seal and verifier, the I184 brief and the finalized parent disposition.
All three supplied detached hashes matched. Their values were written
to `input-authentication.json` before starting the proof.

The seal and verifier were hashed as opaque inputs, not run, imported,
copied or reimplemented. No historical Python was imported as research
implementation. No 23-stage replay, snapshots, new seal framework or
computational certificate was created. Parent controls are reported as
inherited evidence, not checks executed in this round.

One initial file-pattern search was broader than intended and returned
unrelated instruction paths, including sibling-project paths. No
sibling source content was deliberately read or changed, and no sibling
task instructions were used for this project. Subsequent searches
were restricted to the assigned project and focused sources.

## Attempted routes and their disposition

### 1. Automatic descent of brace extendability: not used

It would be invalid to say that two-extendability of $G$ directly
makes the three-edge-frozen residual $G'$ two-extendable. The written
proof instead assumes failure of a single alternating path, derives
an odd shore with cut $\{e,aa',cc'\}$, and contradicts two-extendability
using exactly the disjoint pair $aa',cc'$.

**Outcome:** the first obligation is proved, for every residual
perfect matching and each of its edges. This does not establish
two-extendability of $G'$ or a simultaneous multi-edge avoidance
prescription.

### 2. Alternation or shortest cycle implies Hamiltonicity: failed

The cycle gives connectedness of $R\cup T_Z$, where $R$ is the
pairing of deleted Hamiltonian edges. Hamiltonicity after the toggle
requires connectedness of $S_H\cup T_Z$, where $S_H$ pairs endpoints
of the retained Hamiltonian paths. Replacing $R$ by $S_H$ is the
precise unsupported implication.

The four-incidence calculation in the analytic attempt explicitly
separates these two assertions. It is a formal pairing calculation,
not a graph construction, scan result or fully hypothesized
counterexample. It does not show that Z184 fails for even one instance.

**Outcome:** shortest-cycle selection by itself does not prove the
second obligation. No proof selects connected reconnection among
all cycles and all allowed completions.

### 3. Minimize complement components and improve: incomplete

The finite choice set has a minimum component count, but no exchange
argument was found showing that a minimum greater than one admits a
better single cycle through $e_2$. A subsequent toggle can change the
reference local packing or make the net difference several cycles.
Existence of further alternating cycles supplies neither the sign
of the component-count change nor preservation of the Z184 format.

**Outcome:** no unproved local-improvement rule is used.

### 4. Start from a survivor and extract one difference cycle: incomplete

Complete nonempty survivor fibres give survivor packings, but do not
force their complementary matchings to contain $A$. Even with that
extra property supplied, two matching complements may differ on
several disjoint alternating cycles. A Hamiltonian outcome after all
of them does not justify keeping only the one through $e_2$.

**Outcome:** no one-cycle extraction theorem or E183-to-Z184 converse
was obtained.

### 5. Use another exterior completion of the same local packing: limited

Every completion of fixed $q$ still has type $P$. Exterior freedom
could potentially help choose a connected toggle, and the target
allows some completion, but exterior-only rerouting cannot itself
make the local type survive. Failure for one completion would not
refute the existential target.

**Outcome:** neither the old fixed-local equivalence nor a universal
completion requirement is introduced.

### 6. Invoke pinned Hamiltonicity, edge avoidance or P4: insufficient

The actual source statements were read. They do not specify the
three frozen matching edges, connected complement, survival and
single-cycle difference simultaneously. The auxiliary contracted
graph is not automatically simple or a brace. No hypothesis check
or reduction making those theorems prove Z184 was found.

**Outcome:** no silent strengthening of an upstream statement.

### 7. Promote the incidence pattern to a counterexample: rejected

The incidence calculation supplies no admissible disk $X$, no
verified eleven complete nonempty survivor fibres, no brace proof,
and no exclusion of every $q$-completion. Those obligations cannot
be replaced by a degree-correct pattern.

**Outcome:** no actual counterexample is claimed.

## Preserved historical failures

D168 transfer, M168 typed fullness, deleted-coordinate shortcuts,
failed containments and isolated-toggle failures remain binding.
No attempt here uses them. The original I183 provider failure had
no research verdict; the incomplete unsealed checkpoint remains an
incomplete unsealed historical checkpoint. The completed finalization
does not erase those facts.

The parent authentication/replay and independent finite controls are
accepted as reported. Their three patches, six directed instances,
five controlled matchings per instance and 626 matching cases are
not universal evidence. Eight accepted findings remain eight.

## Validation and reading limits

The proof was checked internally by rederiving the alternating
reachability bijection and the degree identity
$r-s=2+h$. Bounds $r\leq2$, $s,h\geq0$ force the unique shore
configuration; its color imbalance forces one matching crossing,
contradicting the two prescribed continuation edges.

The reconnection criterion was checked in both directions by
contracting and expanding the retained paths. Singleton paths are
retained in the generalized formulation; loops and parallel edge
identities are retained throughout. The exact simple-cycle case has
no singleton paths because the removed edges are a matching.

No numerical tests, graph generation, scans, formal proof-assistant
checks or independent reviewer were used. No global novelty or
priority claim is made. The source manuscript and external cited
proofs were not reread in full. The only mathematical progress
claimed is the elementary first-obligation proof, not a resolution
of Z184 or E183.
