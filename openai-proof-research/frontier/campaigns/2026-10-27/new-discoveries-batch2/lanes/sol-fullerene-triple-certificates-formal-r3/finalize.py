from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipt=json.loads((L/'replay-receipt.json').read_text());assert receipt['status']=='PASS'
for p in L.rglob('*'):
 if p.is_file() and (p.suffix in ['.olean','.ilean','.o','.ir','.c'] or '.olean.' in p.name):p.unlink()
raw=json.loads((L/'coverage.json').read_text())
stats={tag:dict(triples=len(raw[tag]['entries']),good=sum(r['kind']=='good' for r in raw[tag]['entries']),bad=sum(r['kind']=='bad' for r in raw[tag]['entries'])) for tag in ['G','H']}
assert all(s==dict(triples=4960,good=60,bad=4900) for s in stats.values())
failed=[]
for p in sorted(list(L.glob('attempt-*.json'))+list((L/'replay/candidate').glob('attempt-*.json'))):
 r=json.loads(p.read_text());s=p.with_suffix('.log').read_text()
 if r['exit']!=0 or any(x in s.lower() for x in ['panic','error:','rejected']):failed.append(dict(receipt=str(p.relative_to(L)),reported_exit=r['exit'],accepted=False))
for p in (L/'replay/fresh').glob('attempt-*.log'):
 if not p.with_suffix('.json').exists():failed.append(dict(log=str(p.relative_to(L)),kind='tool interruption without completion receipt',accepted=False))
(L/'failures.json').write_text(json.dumps(failed,indent=2)+'\n')
provenance=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),counts=dict(additional=9,total=39,next=40,changed=False),acceptance='root only',full_source='HOLD',novelty='HOLD',external_retrievals=[],historical_denials='Parked; no denied route retried',statistics=stats,archive_sha256=sha(L/'source.zip'),inherited_repair=False,inherited_modules_unchanged=['Literal','InstanceG','InstanceH','Rank','Hulls','Geometry'],replay=receipt)
(L/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
audit=json.loads((L/'audit.json').read_text())
summary=f'''# Actual fullerene triple certificates and real vertices/hulls

30 October 2026. Implementation component CLOSED for actual G/H vertex completeness, convex hulls and all indexed supporting sections. Full source, novelty and acceptance remain HOLD. Counts remain9 additional /39 total / next40; root alone accepts/counts. Solo work, no children, manuscript, shared/git/public/browser/MathDB changes or analytic/facet-edge-cubic next stage.

## Literal real endpoints

`CompleteG.lean` and `CompleteH.lean`, namespace FullereneGeometry, prove:

* `complete_triples_G/H`: every real x feasible for the actual qG/qH, satisfying the equations of any independent active triple, belongs to the range of the actual pG/pH.
* `listed_vertices_G/H`: each of the60 actual listed real points is feasible and has an active triple whose equations uniquely determine that point among ALL real points.
* `complete_vertices_G/H`: `(poly qG/qH).extremePoints ℝ = Set.range pG/pH`, by applying the inherited `complete_vertices_of_triple_certificates` with both actual premises discharged.

`HullG.lean` and `HullH.lean` apply the inherited bridges to those actual equalities and actual compact_G/H:

* `hull_G/H`: `poly qG/qH = convexHull ℝ (Set.range pG/pH)`.
* `section_hull_G/H`: for EVERY i:Fin32, `facetSection qG/qH i = convexHull ℝ {{x ∈ Set.range pG/pH | dot (qG/qH i) x = 1}}`.

These are quantified real statements, not rational table-validity surrogates. No affine dimension, facet/edge exhaustion, cubic adjacency, analytic exponential or full SourceClaim follows in this packet.

## Checked finite certificates and transport

There are4960 sorted distinct triples per graph, split into310 modules of16 arithmetic certificates each (620 arithmetic modules total). All have a checked nonzero integer determinant and a positive-denominator rational point satisfying the three active equations. The untrusted generator obtains this point by rational Cramer arithmetic. Every identity is subsequently kernel-checked: the generator's assertions are not axioms. For each graph60 records identify an actual listed point by exact cross-products;4900 identify one explicit strictly violated inequality. The converse60 listed-point certificates check all32 inequalities and a nonsingular active triple.

DataG/H express integer normals scaled by a positive common D. BindingsG/H prove their coordinatewise equality with the actual real qG/qH and pointwise equality with pG/pH. RealCore proves determinant uniqueness by three polynomial linear-combination identities over ℝ, so active equations force EVERY real x to equal the rational witness. A bad witness then contradicts feasibility; a good witness equals the literal listed point. CompletionCore sorts every independent triple from Rank using injectivity and six order cases. Coverage of every sorted triple is an exact reflexive equality with the finite-index domain; no monolithic4960 arithmetic decide is used.

The new record tables are explicitly noncomputable to suppress unnecessary executable code, preserving their values and kernel proofs. Literal, InstanceG, InstanceH, Rank, Hulls and Geometry remain BYTE-IDENTICAL to the frozen inherited sources. The inherited785-declaration strict audit required no annotation repair.

## Replay, audit and provenance

The final deterministic source archive is `source.zip`, SHA256 `{sha(L/'source.zip')}`. Its clean source-only extraction is replay/fresh. All{receipt['compiler_calls']} completed serial compiler calls passed, with{len(audit['origins'])} mathematical module origins and{audit['owned']} actual declarations reconciled against individual axiom reports. Private/generated names are included. Both partial and unsafe flags, and every transitive type/body dependency, are hard-fail checked; only propext, Classical.choice and Quot.sound occur. No ignorelist. One interrupted audit had no completion receipt and was rerun successfully; its log remains unaccepted evidence. The earlier candidate extraction and all rejected attempts remain evidence; they are not used by the final clean replay. See audit.json, owned-declarations.json, replay-receipt.json, RUN.md and FAILURES.md/failures.json.

All Lean calls use the pinned compiler and9 unchanged package pins with j1 M2700, groupRSS2800MiB CPU210s wall230s, warningAsError=true autoImplicit=false. Helpers use the required512MiB guard with CPU210s wall230s. No caps were raised. Owned compiled objects are removed before final manifest generation. Separate guarded verify.py checks scientific original/copy hashes, inherited source/name preservation, all pins/compiler hash, extracted/archive/source equality, deterministic ZIP regeneration, manifest exclusion of itself/receipt, and absence of owned compiled objects.

Sources were frozen before scientific reading, with original/copy hashes checked before and after. The root r5 disposition, exact r2 sources/summary/failures/harness, original rational realizations and pinned Krein–Milman/finite-convex-hull proof bodies are bound locally. Administrative files are snapshots only. No external retrieval was attempted; denied GitHub/ScienceDirect/Google routes and inaccessible historical intervals remain parked. No current literature/priority clearance is claimed. Novelty/full-source HOLD and independent root acceptance remain outstanding.
'''
(L/'SUMMARY.md').write_text(summary)
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p not in [L/'MANIFEST.json',L/'verification-receipt.json']}
(L/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('finalized',len(manifest),'files;',len(failed),'preserved rejected attempts')
