from pathlib import Path
import hashlib,json,re,collections,zipfile
r=Path(__file__).resolve().parents[1]
import os
os.chdir(r)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
replay=json.loads(Path('extracted/replay-receipt.json').read_text())
negative=json.loads(Path('negative-controls/results.json').read_text())
assert replay['passed'] and negative['passed']
version=Path('extracted/logs/version.log').read_text()
assert '4.34.1' in version and '5045d0056413' in version
after=[]
for x in json.loads(Path('inputs-before.json').read_text()):
 assert sha(x['source'])==sha(x['copy'])==x['sha256']
 after.append(dict(**x,unchanged=True))
Path('inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
for p in Path('inputs/edgepattern-formal-r2/formal').glob('*.lean'):
 assert p.read_bytes()==(Path('formal')/p.name).read_bytes()
sourcehashes={str(p):sha(p) for p in sorted(Path('formal').glob('*.lean'))}
for p,h in sourcehashes.items():assert sha(Path('extracted')/p)==h
for n in ['replay.py','watchdog.py','modules.json']:assert sha('scripts/'+n)==sha('extracted/scripts/'+n)
audit=Path('extracted/logs/replay-AuditR3.log').read_text()
entries=re.findall(r'^DECL (.*?)\nMODULE (.*?)\nUNSAFE (.*?)\nPARTIAL (.*?)\n',audit,re.M)
counts=dict(collections.Counter(x[1] for x in entries))
total=int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',audit)[1]);assert len(entries)==total
assert all(u=='false' and p=='false' for n,m,u,p in entries)
assert not any(x in audit for x in ['⋯','…'])
node_ids=[int(x) for x in re.findall(r'^EXPR_NODE (\d+) ',audit,re.M)]
node_count=int(re.search(r'TOTAL_EXPR_NODES (\d+)',audit)[1])
assert node_ids==list(range(node_count))
roots=[int(x) for x in re.findall(r'^(?:TYPE_NODE |BODY node )(\d+)$',audit,re.M)]
assert all(0<=x<node_count for x in roots)
Path('audit-inventory-counts.json').write_text(json.dumps(dict(total=total,by_module=counts,inventory=[dict(name=n,module=m,unsafe=u,partial=p) for n,m,u,p in entries]),indent=2)+'\n')
receipts=[json.loads(p.read_text()) for p in Path('extracted/logs').glob('*.receipt.json')]+[json.loads(p.read_text()) for p in Path('negative-controls').glob('*.receipt.json')]
assert all(x['killed'] is None and x['peak_sampled_private_rss_bytes']<=6*1024**3 and x['elapsed_seconds']<=140 for x in receipts)
verification=dict(strict_fresh_replay=replay,negative_controls=negative,all_local_declarations_audited=total,full_audit_expression_nodes=node_count,full_audit_encoding='Complete shared Lean.Expr AST; see AUDIT-FORMAT.md',allowed_axioms=['propext','Classical.choice','Quot.sound'],source_identity=sourcehashes,all_11_inherited_modules_byte_identical=True,all_inputs_unchanged=True,peak_final_sampled_private_rss_bytes=max(x['peak_sampled_private_rss_bytes'] for x in receipts),max_final_call_elapsed_seconds=max(x['elapsed_seconds'] for x in receipts),final_verification_no_killed_processes=True,development_failures='Retained in logs and failed-replay-01. Monolithic 2222 evaluation was killed by RSS watchdog, with peak sample 7375745024 bytes; it was replaced by proved-sound 256-mask block certificates. Initial stricter 5 GiB watchdog also killed inherited Concrete during fresh replay; final threshold 5.75 GiB. The initial flat audit exceeded CPU 120 seconds and was replaced by a complete expression DAG audit. Early development reused log names and an early invocation was launched before the prior batch session was drained, so early development overlap was not ruled out; only final replay and negative controls are certified sequential.')
Path('verification.json').write_text(json.dumps(verification,indent=2)+'\n')
endpoints={
'EdgePattern.Concrete.regular':'RegularPattern pattern 3 2',
'EdgePattern.Concrete.exact_girth':'ExactGirth pattern 6',
'EdgePattern.Concrete.expectation_values':'expectation pattern 0 = 2/5 ∧ expectation pattern 1 = 14/5 ∧ expectation pattern 2 = 4/5',
'EdgePattern.Concrete.expectation_separating_value':'(∑ i : Fin 3, alpha i * expectation pattern i) = 67027/67500',
'EdgePattern.MaskR3.complete':'∀ s : Finset (Fin n), ∃ m < 2^n, decode n m = s',
'EdgePattern.MaskR3.decode_inj':'a < 2^n → b < 2^n → decode n a = decode n b → a = b',
'EdgePattern.MaskR3.maxima_eq':'maxima G = (best G).image (decode n)',
'EdgePattern.MaskR3.best_of_checks':'(hne : ms.Nonempty) → (∀ m ∈ ms, m < 2^n ∧ ok G m ∧ size n m = M) → (∀ m < 2^n, ok G m → size n m ≤ M ∧ (size n m = M → m ∈ ms)) → best G = ms',
'EdgePattern.TreeModelsR3.distance_eq':'rootDistance (pattern k) x = level x',
'EdgePattern.TreeModelsR3.expectation_eq':'expectation (pattern k) i = occupancy k i',
'EdgePattern.TreeModelsR3.all_81':'∀ k : Counts, 1 ≤ ∑ i : Fin 3, Concrete.alpha i * expectation (pattern k) i',
'EdgePattern.TreeModelsR3.bound_of_iso':'RootedIso T (pattern k) → 1 ≤ ∑ i : Fin 3, Concrete.alpha i * expectation T i',
'EdgePattern.TreeModelsR3.tree_bound_of_classification':'ClassifiedCubicTrees → CubicTreeBound',
'EdgePattern.TreeModelsR3.neg_conjecture_of_classification':'ClassifiedCubicTrees → ¬ Conjecture2.{0}' }
result={'342414':dict(status='PARTIAL_ZERO_CREDIT',credit=0,root_accepted=False,refutation_proved=False,unconditional_endpoint=None,proved_endpoints=endpoints,declarations=dict(total_including_generated=total,by_module=counts),canonical_forms_semantically_evaluated=81,classification_proved=False,universal_tree_bound_proved=False,all_11_inherited_modules_byte_identical=True,inputs_unchanged=True,prior_art_gate='Inherited unchanged; not repeated',packet='edgepattern-r3-partial-source.zip',verification='verification.json',gaps='GAPS.md',no_child_agents=True,no_git=True,no_shared_ledger_edits=True)}
Path('results.json').write_text(json.dumps(result,indent=2)+'\n')
Path('SUMMARY.md').write_text(f'''# MathDB 342414 — semantic finite evaluation, partial and zero credit

The unconditional refutation is not completed. Arbitrary-tree classification remains unproved, and root acceptance is not claimed.

This continuation closes the canonical-evaluation gap with a proved-sound Nat.testBit mask enumerator. It proves completeness of subset encoding and exact agreement with the literal maximum-independent-set finset. Every canonical graph has at most 14 vertices. Actual root distances, layers and uniform maximum-set expectations are proved, then all 81 labelled four-leaf-count forms satisfy the exact rational separating bound. The computational certificates are split into blocks of at most 256 masks. The old arithmetic Canonical.State recursion is not used as a semantic assumption.

BridgeR3 transfers the bound through an explicit rooted isomorphism on arbitrary finite vertex types, then proves ClassifiedCubicTrees → CubicTreeBound and ClassifiedCubicTrees → ¬ Conjecture2.{{0}}. ClassifiedCubicTrees is not proved or postulated. Thus the requested unconditional endpoint, including the requested universe scope, is absent. See GAPS.md.

All eleven inherited modules are byte-identical. One hundred required input files were hash-bound before copying and rechecked afterward. The prior-art gate was not repeated. No child agents, git operations or shared-ledger changes were used.

Validation passed for this partial certificate: fresh sanitized strict source-only replay, leanchecker on all 266 modules, complete expression-DAG type/body/safety/axiom audit of {total} local declarations including generated declarations, seven false-statement controls and existing-object refusal. Only propext, Classical.choice and Quot.sound are allowed. Final verification processes stayed within the caps. Development failures remain recorded: the initial monolithic 14-vertex evaluation was killed by the RSS watchdog after a sample exceeded 6 GiB, and an initial 5 GiB trigger killed the inherited Concrete module. The final replay uses 5.75 GiB headroom and bounded block certificates; those failed attempts are not passing verification evidence. The first flat audit exceeded the CPU cap and was replaced by the complete expression-DAG encoding in AUDIT-FORMAT.md. Early development reused log filenames, and overlap at the tail of its initial batch was not ruled out. Only final replay and negative controls are certified sequential; see REPRODUCE.md.

The source-only packet contains the portable driver, sources, hash manifests, receipts, complete final audit and negative-control evidence. Results and declaration counts are in results.json and audit-inventory-counts.json. No acceptance or campaign-count change is asserted.
''')
Path('GAPS.md').write_text(Path('GAPS.md').read_text().replace('the blocked evaluation certificates are undergoing strict replay','all 81 blocked evaluation certificates passed strict fresh replay and leanchecker').replace('The new reduction is intended to leave only classification as the hypothesis. Final verification status is recorded in results.json, not inferred from this draft.','The proved new reduction leaves classification as the explicit hypothesis. Verification status is recorded in results.json.'))
files=[*Path('formal').glob('*.lean'),*Path('scripts').glob('*.py'),*Path('scripts').glob('*.json'),*[Path(n) for n in ['SUMMARY.md','GAPS.md','REPRODUCE.md','AUDIT-FORMAT.md','PRIOR-ART.md','statement-correspondence.md','inputs-before.json','inputs-after.json','results.json','verification.json','audit-inventory-counts.json']],*Path('negative-controls').glob('*.lean')]
with zipfile.ZipFile('edgepattern-r3-partial-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,p.as_posix())
 z.write('extracted/replay-receipt.json','evidence/replay-receipt.json')
 for p in Path('extracted/logs').glob('*'):z.write(p,'evidence/'+p.name)
 for p in Path('negative-controls').glob('*.log*'):z.write(p,'evidence/negative-'+p.name)
 z.write('negative-controls/results.json','evidence/negative-controls.json')
 for p in Path('logs').glob('*.log*'):z.write(p,'development/'+p.name)
 for p in Path('logs').glob('*.lean'):z.write(p,'development/'+p.name)
 for folder in ['failed-replay-01','failed-replay-02']:
  for p in Path(folder,'logs').glob('*'):z.write(p,'development/'+folder+'/'+p.name)
 assert not any(n.endswith(('.olean','.ilean','.ir')) for n in z.namelist())
Path('packet-receipt.json').write_text(json.dumps(dict(packet='edgepattern-r3-partial-source.zip',sha256=sha('edgepattern-r3-partial-source.zip'),source_only=True,formal_source_sha256=sourcehashes,source_and_replay_driver_identical_to_successful_fresh_replay=True),indent=2)+'\n')
print(json.dumps(dict(status='PARTIAL_ZERO_CREDIT',declarations=total,packet_bytes=Path('edgepattern-r3-partial-source.zip').stat().st_size)))
