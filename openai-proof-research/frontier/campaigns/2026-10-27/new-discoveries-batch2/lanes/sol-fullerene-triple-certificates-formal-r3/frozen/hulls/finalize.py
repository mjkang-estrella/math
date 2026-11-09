from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
audit=json.loads((L/'audit.json').read_text());replay=json.loads((L/'replay-receipt.json').read_text())
assert audit['status']==replay['status']=='PASS'
summary='''# Vertices and hulls: staged incomplete implementation

30 October 2026. Solo; no children, shared writes, git commands, public changes, browser, MathDB, analytic development or manuscript. Counts 9 additional / 39 total / next40 are unchanged. Novelty/acceptance HOLD. No SourceClaim.

## Exact proved interfaces

`Geometry.lean`, namespace FullereneGeometry, preserves all three inherited mathematical modules byte-identically.

* `active_independent_triple q x hk`: for any finite family q in Fin3→ℝ, if every direction annihilating the active normals at x is zero, there exists ids:Fin3→Fin n with every selected normal active at x and `LinearIndependent ℝ (fun k => q (ids k))`. No feasibility or generic-position premise is required here. The proof makes active linear functionals span the whole dual using trivial annihilator, extracts a basis contained in that set, uses dual dimension=3 to reindex it, chooses the corresponding active indices, and pulls independence back along the explicitly linear normalMap. Independence also implies the three indices are distinct. This closes obligation1 in its general finite-dimensional form.
* `extreme_active_independent_triple q x hx`: applies the above to the actual mathlib extreme point predicate using the inherited active_kernel_trivial theorem.
* `complete_vertices_of_triple_certificates q p complete listed`: concludes `(poly q).extremePoints ℝ = Set.range p`, provided every feasible point satisfying any independent active triple belongs to range p, and every listed point is feasible and uniquely determined by an active triple. The universal completeness premise is explicit; it has NOT been discharged for G or H.
* `hull_of_complete_vertices q hc p hv`: if the actual polyhedron is compact and its actual extreme points equal the finite range p, then `poly q = convexHull ℝ (Set.range p)`.
* `section_hull_of_complete_vertices q hc p hv i`: under the same hypotheses, `facetSection q i = convexHull ℝ {x ∈ Set.range p | dot (q i) x = 1}`. This holds even for an empty section and makes no facet-completeness or dimension assumption. Closedness, compactness and convexity of the actual section are proved. The inherited extreme-face theorem gives its extreme points as exactly the global extreme points on that section; conversely a global extreme point lying on the section remains extreme there.

The hull proofs inspect and use pinned `closure_convexHull_extremePoints` from Mathlib/Analysis/Convex/KreinMilman.lean. Finite vertex range (or its incident subset) has closed convex hull by `Set.Finite.isClosed_convexHull` from Convex/Topology.lean, so the closure is rigorously removed. No endpoint/rank induction is assumed. All pinned inspected proof bodies are frozen under mathlib/ with original/copy hashes.

## Exact residuals

Obligation2 remains OPEN. Neither `(poly qG).extremePoints ℝ = Set.range pG` nor its H analogue has been proved. Inherited coordinate-check.json remains Python evidence only. The new experimental RationalEnumeration.lean attempts the entire sorted-triple domain, including nonsingularity and feasible-intersection membership, via rational Cramer coordinates and kernel decide. It does NOT compile; its failed declarations are excluded from the proof archive and audit. No checked enumeration or real-cast/uniqueness bridge is claimed. A proof-producing split arithmetic certificate scheme and its real interpretation are still needed for all4960 triples in EACH instance, plus feasibility/extremality of all listed points. Checking only the60 supplied points cannot discharge the explicit completeness premise.

Obligation3 is proved as a general conditional bridge, but remains OPEN as actual G/H equalities until obligation2 supplies hv. Existing compact_G and compact_H discharge hc. No assertion that actual sections/facets/edges/cubic adjacency are complete is made; the subsequent affine dimension, edge exhaustion, cubic incidence and facet adjacency work remains outside this assignment.

## Validation and limits

Fresh deterministic source-archive extraction compiled all four mathematical modules serially, followed by separate inherited-module and Geometry audits under unchanged bounds. Every actual owned-origin declaration, including private/generated declarations, has an individual axiom report; transitive type/body dependencies are checked for unsafe declarations. Only propext, Classical.choice, Quot.sound are allowed. The first combined audit exceeded M2700 and is preserved; separate audit passes avoid importing both large coordinate instances together with the heavier geometry dependencies. Their owned sets are reconciled as a union. All owned compiled artifacts, including failed replay outputs, are removed after successful replay.

No external retrieval was attempted. Denied historical GitHub/ScienceDirect/Google routes remain parked; no current literature or priority clearance is claimed. This lane is formal geometry implementation only. Scientific original/copy hashes and nine package pins are checked separately after final writes; administrative files are snapshots, not scientific premises. See RUN.md, audit.json, replay-receipt.json, source-bindings.json, mathlib-bindings.json, FAILURES.md and verification-receipt.json.
'''
summary=summary.replace('`Geometry.lean`, namespace FullereneGeometry', '`Geometry.lean` reexports `Rank.lean` and `Hulls.lean`, namespace FullereneGeometry')
summary=summary.replace('all four mathematical modules serially, followed by separate inherited-module and Geometry audits', 'the inherited modules, Rank, Hulls and their Geometry import interface serially, followed by separate inherited-module, Rank and Hulls audits')
summary=summary.replace('The first combined audit exceeded M2700 and is preserved; separate audit passes avoid importing both large coordinate instances together with the heavier geometry dependencies. Their owned sets are reconciled as a union.', 'The combined audit and two Geometry-only inventory attempts exceeded M2700 and are preserved. The proved module was then split into Rank and Hulls without changing theorem statements or proofs, reducing per-pass imports. Their exact module-header declaration inventories and the inherited-module inventory are reconciled as a union; every private/generated name is covered. Geometry is an import-only interface and declares no constants.')
summary += '\nThe audit command implementations are precompiled separately in AuditSupportRank/Hulls, importing only Lean, before use against mathematical modules. These elaborator harness modules are outside the mathematical declaration universe. The audited mathematical origins are exactly Literal, InstanceG, InstanceH, Rank and Hulls; Geometry has no declarations. This avoids compiling meta command implementations in an already large mathematical import environment without raising any resource cap. Failed replay directories remain intact except for removed owned compiled artifacts.\n'
summary=summary.replace('exact module-header declaration inventories', 'exact environment module-origin declaration inventories').replace('importing only Lean,', 'using the narrower Lean.Elab.Command/Print imports,').replace('without raising any resource cap.', 'without raising any resource cap. The earlier module-header approach and broad Lean import attempts are preserved as failures.')
summary += '\nFinal extracted compilation/audit is replay/fresh-6. All14 serial compiler calls succeeded. Full attempt logs (not the runner console tail) reconcile785 owned declarations; the final parser correction required no scientific edit or compiler rerun. Audit safety traversal counts are recorded individually in audit.json. The previous774 declarations are preserved, and11 new mathematical declarations are audited; these receive no discovery credit.\n'
(L/'SUMMARY.md').write_text(summary)
(L/'FAILURES.md').write_text('''# Preserved failures

All attempt-NNN logs and JSON records are retained. Early Geometry attempts had basis-namespace, index-type, reindex conversion and extensionality errors; the final Geometry module compiles without diagnostics. Probe.lean is a failed API probe, outside the proof archive.

RationalEnumeration attempts initially referenced unavailable notation/tactic imports, then had a nested-vector translation bug. The final complete-domain generated candidate has well-formed vector data but `decide +kernel` failed to reduce the rational arithmetic Decidable instance to isTrue/isFalse. It proves no enumeration result; no generated candidate is imported into proved modules. Its final attempt consumed about18s, without a resource-cap increase. The experimental candidate and generator are retained for inspection.

The first combined Inventory replay, two Geometry-only attempts, and a Rank-only attempt hit Lean interpreter excessive memory at M2700. replay/fresh through fresh-3 retain diagnostics. Splitting the mathematical source into Rank/Hulls reduces imports per inventory; exact module-header declaration metadata avoids scanning all imported declarations; precompiling the audit command implementations with only Lean avoids compiling these meta commands in the large mathematical environment. The final fresh extraction audits inherited origins, Rank, and Hulls separately, union-reconciles all names and axiom reports, and traverses every owned type/body dependency. All caps are unchanged. No external source access failure was retried. The cancellation helper found no running enumeration process when invoked; no cancelled proof was accepted.
''')
with (L/'FAILURES.md').open('a') as f:
 f.write('\nFurther broad-import audit attempts in fresh-4/fresh-5 also exceeded M2700. The final narrow-import audit in fresh-6 passed all14 compiler calls in about86s total. Initial receipt reconciliation mistakenly parsed the runner console tail instead of full attempt logs, reporting51 names rather than785; package.py was corrected and guarded reconciliation of the unchanged complete logs passed. No compiler or theorem failure was hidden or converted into acceptance.\n')
(L/'provenance.json').write_text(json.dumps(dict(date=datetime.datetime.now(datetime.timezone.utc).isoformat(),novelty='HOLD',source_claim=False,counts_changed=False,scope='obligation1 closed; obligation2 open; obligation3 conditional',archive_sha256=sha(L/'geometry-source.zip'),owned_declarations=audit['owned_declarations'],source_freeze='source-bindings.json',mathlib_freeze='mathlib-bindings.json',external_retrievals=[]),indent=2)+'\n')
excluded={'MANIFEST.json','verification-receipt.json'}
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded}
(L/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('finalized',len(manifest),'files')
