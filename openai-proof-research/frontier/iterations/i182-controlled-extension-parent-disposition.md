# I182 parent disposition: exact reduction to survival, still unresolved

2026-10-11. **Technical only. Eight accepted, two remaining.**
E182, E181, H180 and L179 remain unresolved. No ninth contribution is
nominated.

## Scope and proof review

The parent read the complete [report](i182-controlled-extension.md),
analytic attempt, mathematical/research code, authentication, runner,
packager, prevalidator, verifier, failures and literature receipt.
The stipulated upstream pin and the previously read actual main,
edge-avoidance and prescribed-path statements are unchanged.
There is no upstream truth audit.

The reduction lemma is proved at the correct level and is correct.
Deleting the alternating half $A$ bijects $A$-containing perfect
matchings of $G$ with perfect matchings of the derived graph
$G' = G - V(C)$, whose four continuation terminals have degree two and
whose other vertices are cubic. Hence $G' - M'$ is a disjoint union of
cycles and exactly two terminal paths, and $G - M$ is one Hamiltonian
cycle exactly when no closed component survives and the two paths pair
the terminals crosswise. Cut edges and ports lie in $G'$, so the port
data of the complement is read off from $G' - M'$. The quotient
multigraph remark for coinciding terminals is correctly scoped and is
not needed by the retained instances.

The claim that the topological half is always payable is also correct:
because the lost toggle $q$ lies in the *complete* lost fibre, an
exterior partner glues it to a Hamiltonian cycle whose complement is an
$A$-containing perfect matching. So controls (1) and (2) of E182 are
simultaneously achievable under the hypotheses, with the lost packing
$q$ itself as the local restriction. What remains is exactly
CPTP-survival: the provably nonempty cross-paired acyclic two-path
population of $G'$ must contain a member whose port pairing and cut
usage form one of the eleven survivor types rather than the lost types
$P=(01;01)$ or $D=(0134;01,34)$. The parent's own reading confirms the
three stipulated theorems do not supply this: brace two-extendability
prescribes two edges in the matching, not complement pairing plus port
survival; the pinned P4 theorem prescribes one three-edge path, not two
disjoint contracted edges with a survival condition; edge avoidance is
pure existence. This is strictly sharper than I181's isolation.

The finite certificate on the retained graph is exactly scoped: three
internal port-disjoint two-square patches, six directed instances, and
on each exactly five controlled matchings hitting survivor fibres
5, 6, 9 — precisely the helper products. It is finite confirmation, not
a general proof, and the report says so.

## Independent validation

[Parent detached authentication and sealed replay](../experiments/i182-parent-verification.json)
pass: **25 owned files, 1,014 strict inputs byte-checked by the parent
harness, four separate contexts** (drift-exempt, recorded). Detached
report, seal and verifier anchors match the supplied out-of-band hashes
exactly; the I175–I181 ancestor chain (94/59/78/81/122/44/29 owned) and
all sixteen I181 parent evidence bindings including the final
integration receipt agree. The stored mandatory and extension payloads
re-hash to the prevalidation double-replay digests after removal of the
volatile runtime field.

Parent sealed replay **PASS** (mandatory about 3.37 seconds, extension
about 0.07 seconds): both diagnostics replay byte-identically, eight
probes blocked, empty process stderr, and all 1,014 strict bindings
unchanged before and after. No file is resealed. This is a Python audit
guard, not an OS sandbox; clean-clone reconstruction is untested.

The [independent parent checker](../experiments/i182-parent-certificates.py)
reuses only the committed parent path-packing chain and is otherwise
fresh code (its own exact-cover matching enumerator and DFS components;
no I182 source executed). Its
[receipt](../experiments/i182-parent-certificates.json) verifies:

- the patch census independently: exactly three internal port-disjoint
  two-square patches and the four excluded pairs with matching reasons;
- all six directed lost–lost instances independently from the complete
  lost fibre (five packings, re-derived);
- the reduction lemma on **all 626** derived-graph matchings, both
  directions, with the forced degree pattern and the parallel-pairing
  two-cycle case;
- the full per-instance classification: 8 Hamiltonian, 5 controlled,
  3 lost (all type $P$), 26/26/22/22/22/22 parallel-pairing and
  77/77/72/72/70/70 closed-component failures;
- the exact helper-product correspondence: 3 opposite-half helpers,
  5 single-cycle exterior products equal to the 5 controlled matchings,
  9 equal-pairing products correctly two-cycle and excluded;
- on every instance, one lost matching is the $q$-completion itself,
  confirming that controls (1)+(2) are payable and survival alone is
  unpaid.

It passes on its first run. The inherited 22-stage control replay is
covered by byte-authenticated sealed replay and prior independent
parent reviews, not a new population rescan.

## Protocol deviations and verifier weaknesses (disclosed, preserved)

- The sealed verifier was corrected twice *after an initial seal
  existed*: first to fix four verifier-side count assertions (payloads
  unchanged), then to add the mandated eight-probe harness. The stale
  seals were removed and the inventory/prevalidation/seal regenerated;
  `failures.md` records both corrections. The single-seal policy was
  therefore violated in development and restored only by resealing.
  The parent accepts the final seal as the package seal because every
  sealed byte authenticates, both diagnostics replay byte-identically,
  and the correction history is fully retained — but this is a
  deviation from the one-exclusive-seal discipline and is recorded as
  such.
- The sealed `verify182.py` does not itself byte-check the 1,014 strict
  ancestor bindings or the four contexts; that check is supplied by the
  parent harness (`i182-parent-validate.py`).
- The verifier's forged-owned-source probe is vacuous: inventory
  `owned_sha256` values are nested records, so its equality test
  against a bare hex digest can never hold and the probe always takes
  the blocked path. The parent validator checks the same forgery
  condition non-vacuously through the nested digest.
- The seal and inventory embed absolute checkout paths; the package
  hashes are therefore machine-location specific. Portability was never
  claimed; clean-clone reconstruction remains untested.
- The retained I180/I181 `image_minor` string-versus-integer
  discrepancy is handled by explicit Fraction coercion and recorded;
  no ancestor byte changed.

Parent-side development corrections: the first detached validator run
assumed bare hex strings for inventory digests; the rows are nested
records. A parent transcription fix only; no child artifact changed.

## Retained limits

All four failed mandatory attempts, the pre-freeze scoping probes and
the debug print are retained with exact causes and empty captures.
Literature reading covers the actual pinned statements; excerpt-level
leads remain non-authoritative. This is a conditional technical result:
it does not satisfy the substantial-finding gate. Universal high-loss
brace, exchange, (T), Q164, H180, L179, E181 and CPTP-survival remain
open.

## Next bounded step

[I183's brief](iteration183-cptp-survival-brief.md) takes the reduced
problem as its single target: decide CPTP-survival for the derived
quadruple $(G'; a',b',c',d')$ — prove that the lost $(01;01)$ exterior
routing of the $q$-completion can always be re-routed inside the fixed
exterior $Y$ to one of the eleven surviving pairings while preserving
the cross pairing of the two terminal paths, or refute it by an actual
written $X$ meeting every H180 hypothesis in which every cross-paired
acyclic complement is lost. No broader census, parameter sweep or
verdict bundling is authorized.

Parent documents and shared ledgers are finalized and preflight checked
before dispatch. Actual dispatch/readback and final exact staging scope
are archived separately. Only `openai-proof-research` is published.
