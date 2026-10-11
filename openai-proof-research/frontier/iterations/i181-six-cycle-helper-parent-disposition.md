# I181 parent disposition: proved local reattachment, unpaid controlled extension

2026-10-11. **Technical only. Eight accepted, two remaining.**
E181, H180 and L179 remain unresolved. No ninth contribution is nominated.

## Scope and proof review

The parent read the complete [report](i181-six-cycle-helper.md),
analytic attempt, mathematical/research code, authentication, runner,
packager, prevalidator, verifier, failures and literature receipt.
The stipulated upstream pin and the previously read actual main,
edge-avoidance and prescribed-path statements are unchanged.
There is no upstream truth audit.

The local reattachment lemma is proved at the correct level of
generality. On the two-face disk with simple boundary
$C=(x,a,b,y,d,c,x)$, chord $xy$ and alternating halves
$A=\{xa,by,dc\}$, $B=\{ab,yd,cx\}$, every cycle vertex is internal
and cubic, so degree two forces the chord and all four continuation
edges on either side. Both forced local sets route the four
continuation terminals as $a$–$b$ and $c$–$d$. Replacing one local
routing by the other therefore preserves the component partition of
every unchanged external segment decomposition, including singleton,
loop and parallel-edge components, which the formal certificate
retains rather than contracts away. Consequently, once an actual
cycle-free same-type survivor helper $u$ using the opposite half
exists, $v=u\mathbin{\triangle}E(C)$ is automatically spanning,
degree-correct, cycle-free and same-type, and $p+u=q+v$ holds
coordinatewise because both pairs toggle exactly $E(C)$.

The report correctly isolates the unpaid step as a controlled
three-edge alternating-half extension: a perfect matching containing
the three disjoint edges of $A$ whose complement is one Hamiltonian
cycle and whose local restriction lies in one of the eleven stipulated
nonempty survivor fibres. The parent's own reading confirms the three
existence theorems do not supply it: brace two-extendability covers
two disjoint edges, not this controlled three-edge class; the pinned
P4 theorem can force one three-edge path such as $c-x-y-d$ but not
simultaneously the separate edge $ab$, the four continuation edges,
a survival condition or the fibre; edge avoidance is an existence
statement without simultaneous controls. The observation that a
global Hamiltonian completion of the lost toggle $q$ yields an
$A$-containing perfect matching with Hamiltonian complement — hence
that $A$ is matchable — is correct but its local restriction is the
lost packing $q$ itself, so it pays matchability, not the controlled
survivor condition. No new graph test was run and none was authorized.

## Independent validation

[Parent detached authentication and sealed replay](../experiments/i181-parent-verification.json)
pass: **29 owned files, 972 strict inputs, four separate contexts**.
Detached report, seal and verifier anchors match the supplied
out-of-band hashes exactly. Membership, exclusive roots, the
I175–I180 ancestor control chain (94/59/78/81/122/44 owned) and the
15 parent evidence bindings agree. The stored mandatory and topology
payloads re-hash to the prevalidation double-replay digests after
removal of the volatile runtime field.

Parent sealed replay **PASS** (mandatory double replay about
3.4 seconds per pass; topology about 0.01 seconds): two byte-identical
payloads per diagnostic, eight blocked probes, empty process stderr,
unchanged strict/context/membership/control-order state before and
after. Post-ledger replay is separately recorded by integration.
No file is resealed. This is a Python audit guard, not an OS sandbox;
clean-clone reconstruction is untested.

The [independent parent checker](../experiments/i181-parent-certificates.py)
uses only fresh parent standard-library code — its own subset
enumeration, union-find with parallel-edge degree retention, pairing
generation and component walks; no I181 source is executed, imported
or compiled. Its [receipt](../experiments/i181-parent-certificates.json)
verifies independently:

- **Patch forcing:** among all $2^{11}$ local edge subsets of the
  abstract patch with correct internal degrees, exactly one uses a
  given alternating half of $C$; it is forced to contain the chord
  and all four continuation edges, has no cyclic local component, and
  induces the terminal pairing $\{a'b',c'd'\}$. Both halves induce
  the same pairing.
- **Reattachment invariance:** for all 120 external perfect segment
  pairings (15 at two ports, 105 at four ports), reattaching with
  either half preserves the cyclic-component count and the port
  pairing, loops and parallel pairs counted as cycles. The full
  recomputed table is byte-identical to the retained sealed topology
  payload (120 rows).
- The report's quoted routings $A\to[[1,0,3,2],[4,5]]$ and
  $B\to[[1,2],[4,3,0,5]]$ match independent component walks.

The inherited control replay (twelve indexed controls, C171, G6/G10,
first P8, I176 k6, I177 absorption, I178 presentation, I179 lock,
parent helper, I180 helper graph) reproduces path distances
8,8,8,6,0, ranks 4,5,5, 99 lost-output cycle rejections and the
twelve exact forward witnesses; those claims were independently
parent-verified in prior rounds and are covered here by
byte-authenticated replay, not a new population rescan.

Parent-side development corrections: the first detached validator
assumed trailing slashes in the inventory's exclusive-roots strings;
the first parent certificate run compared JSON-ified edge lists as
set members and walked degree-1 starts without a first step. All
three were parent transcription bugs in fresh parent code, corrected
without touching any sealed evidence; no child artifact changed.

One verifier design deviation surfaced at integration time: the sealed
`verify181.py` fatally rejects any change to the four ledger contexts
after the freeze, although the mandated policy declares exactly those
four contexts historical-drift exempt with current bytes recorded.
Sealed evidence is not edited. The parent replay above completed
before ledger finalization with unchanged bindings, and post-ledger
replay uses the parent drift-tolerant harness
[`i181-parent-replay.py`](../experiments/i181-parent-replay.py):
same package authentication, frozen-reader double replays
byte-identical to both retained payloads, unchanged strict and
membership bindings, contexts recorded as drifted. Both ledger-drift
replays pass; strict bindings are unchanged before and after.

## Retained limits

The prevalidation `read_json` injection failure is correctly retained
with empty captures; the corrected prevalidator and verifier reproduce
the runner's frozen-reader injection. All four mandatory schema
attempts, the schema probes and the exclusive-output guard failure
remain sealed and unchanged. Literature reading stays excerpt-level
except the actual pinned theorem statements; no novelty clearance.
This is a conditional technical result: it does not satisfy the
substantial-finding gate. Universal high-loss brace, exchange, (T),
Q164, H180, L179 and now E181's controlled extension remain open.

## Next bounded step

[I182's brief](iteration182-controlled-extension-brief.md) takes the
report's own isolated missing condition as the single target: prove
or refute the controlled three-edge alternating-half extension under
the exact H180 graph/interface/brace hypotheses. A proof must produce
the $A$-containing perfect matching with Hamiltonian complement and
identify its local restriction in a survivor fibre; a refutation must
be an actual written construction meeting every hypothesis in which
every such matching has a lost local restriction. No broader census,
parameter sweep or verdict bundling is authorized.

Parent documents and shared ledgers are finalized and preflight
checked before dispatch. Actual dispatch/readback and final exact
staging scope are archived separately. Only `openai-proof-research`
is published.
