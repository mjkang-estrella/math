from pathlib import Path
import json,hashlib,re,zipfile,collections
root=Path(__file__).resolve().parents[1]
import os
os.chdir(root)
replay=json.loads(Path('extracted/replay-receipt.json').read_text())
neg=json.loads(Path('negative-controls/results.json').read_text())
assert replay['passed'] and neg['passed']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
after=[]
for x in json.loads(Path('inputs-before.json').read_text()):
 assert sha(x['source'])==sha(x['copy'])==x['sha256']
 after.append(dict(source=x['source'],copy=x['copy'],sha256=x['sha256'],unchanged=True))
Path('inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
for p in Path('inputs/edgepattern-formal-r1/formal').glob('*.lean'):assert p.read_bytes()==(Path('formal')/p.name).read_bytes()
sourcehashes={str(p):sha(p) for p in sorted(Path('formal').glob('*.lean'))}
for p,h in sourcehashes.items():assert sha(Path('extracted')/p)==h
for n in ['replay.py','watchdog.py']:assert sha('scripts/'+n)==sha('extracted/scripts/'+n)
audit=Path('extracted/logs/replay-AuditR2.log').read_text()
entries=re.findall(r'^DECL (.*?)\nMODULE (.*?)\nUNSAFE (.*?)\nPARTIAL (.*?)\n',audit,re.M)
counts=dict(collections.Counter(x[1] for x in entries))
total=int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',audit)[1]);assert len(entries)==total
assert all(u=='false' and p=='false' for n,m,u,p in entries)
assert not any(x in audit for x in ['⋯','…'])
Path('audit-inventory-counts.json').write_text(json.dumps(dict(total=total,by_module=counts,inventory=[dict(name=n,module=m,unsafe=u,partial=p) for n,m,u,p in entries]),indent=2)+'\n')
receipts=[json.loads(p.read_text()) for p in Path('extracted/logs').glob('*.receipt.json')]+[json.loads(p.read_text()) for p in Path('negative-controls').glob('*.receipt.json')]
assert all(r['killed'] is None and r['peak_sampled_private_rss_bytes']<=6*1024**3 and r['elapsed_seconds']<=140 for r in receipts)
verification=dict(strict_fresh_replay=replay,negative_controls=neg,all_local_declarations_audited=total,allowed_axioms=['propext','Classical.choice','Quot.sound'],source_identity=sourcehashes,all_r1_modules_byte_identical=True,all_inputs_unchanged=True,peak_sampled_private_rss_bytes=max(r['peak_sampled_private_rss_bytes'] for r in receipts),max_call_elapsed_seconds=max(r['elapsed_seconds'] for r in receipts),no_killed_verification_processes=True)
Path('verification.json').write_text(json.dumps(verification,indent=2)+'\n')
endpoints={
'EdgePattern.edist_iso':'H.edist (e x) (e y) = G.edist x y',
'EdgePattern.RootedIso.distance_eq':'rootDistance Q (e.iso x) = rootDistance P x',
'EdgePattern.RootedIso.layer_map':'(layer P i).map e.iso.toEquiv.toEmbedding = layer Q i',
'EdgePattern.maxima_map':'(maxima G).map (Equiv.finsetCongr e.toEquiv).toEmbedding = maxima H',
'EdgePattern.RootedIso.expectation_eq':'expectation Q i = expectation P i',
'EdgePattern.Concrete.distance_values':'rootDistance pattern v = distanceTable v',
'EdgePattern.Concrete.layer_eq':'layer pattern i = layers i',
'EdgePattern.Concrete.regular':'RegularPattern pattern 3 2',
'EdgePattern.Concrete.exact_girth':'ExactGirth pattern 6',
'EdgePattern.Concrete.expectation_values':'expectation pattern 0 = 2/5 ∧ expectation pattern 1 = 14/5 ∧ expectation pattern 2 = 4/5',
'EdgePattern.Concrete.expectation_separating_value':'(∑ i : Fin 3, alpha i * expectation pattern i) = 67027/67500',
'EdgePattern.Concrete.expectation_separating_lt_one':'(∑ i : Fin 3, alpha i * expectation pattern i) < 1',
'EdgePattern.neg_conjecture_of_tree_bound':'CubicTreeBound → ¬ Conjecture2.{0}' }
results={'342414':dict(status='PARTIAL_ZERO_CREDIT',credit=0,root_accepted=False,refutation_proved=False,full_literal_endpoint=None,partial_endpoints=endpoints,declarations=dict(total_including_generated=total,by_module=counts),closed_r1_gap_items=[2,4,5],open_r1_gap_items=[1,3],partially_closed_r1_gap_items=[6],universal_tree_bound_proved=False,verification='verification.json',gaps='GAPS.md',packet='edgepattern-r2-partial-source.zip',prior_art_gate='Inherited unchanged; not repeated; inherited limitations remain',r1_modules_byte_identical=True,inputs_unchanged=True,no_child_agents=True,no_git=True,no_shared_ledger_edits=True)}
Path('results.json').write_text(json.dumps(results,indent=2)+'\n')
Path('SUMMARY.md').write_text(f'''# MathDB 342414 continuation — partial, zero credit

No unconditional refutation of EdgePattern.Conjecture2 is proved. Root acceptance is not claimed.

This continuation closes r1 GAPS items 2, 4 and 5: rooted isomorphisms preserve distances, layers and uniform maximum-independent-set expectations on arbitrary finite vertex types; the witness has the actual stated layers, RegularPattern 3 2 and ExactGirth 6; its actual expectation is (2/5, 14/5, 4/5), with separating value 67027/67500 < 1. No pointwise maximum-independent-set bound is used.

The proved reduction CubicTreeBound → ¬ Conjecture2.{{0}} discharges the witness and finite convex-separation combination. Its premise is not proved. Arbitrary-tree classification and canonical recursion soundness remain open (items 1 and 3), so item 6 remains conditional. See GAPS.md for exact obligations.

All six r1 modules are byte-identical. Five additional modules supply the continuation and full audit. The required inputs were hash-bound before copying and rechecked unchanged afterward. The prior-art gate was not repeated. Its inherited limitations remain.

Validation: a fresh extracted, source-only strict replay passed; leanchecker passed for all eleven modules; the full audit covered {total} local declarations including generated declarations, recording complete types and opaque bodies, safety flags and transitive axioms. Only propext, Classical.choice and Quot.sound occur. Three false-statement controls and existing-olean refusal passed. Verification processes stayed within the stated caps. The packet contains its portable replay driver and evidence.

The immutable audit driver modules themselves introduce no logical declarations. Full type/body output is evidence/replay-AuditR2.log in the packet and extracted/logs/replay-AuditR2.log in the lane. Results and declaration counts are in results.json and audit-inventory-counts.json.
''')
files=[*Path('formal').glob('*.lean'),*[Path('scripts')/n for n in ['replay.py','watchdog.py','negative.py','finalize.py']],*[Path(n) for n in ['SUMMARY.md','GAPS.md','REPRODUCE.md','statement-correspondence.md','PRIOR-ART.md','PRIOR-ART.json','inputs-before.json','inputs-after.json','results.json','verification.json','audit-inventory-counts.json']],*Path('negative-controls').glob('*.lean')]
with zipfile.ZipFile('edgepattern-r2-partial-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,p.as_posix())
 z.write('extracted/replay-receipt.json','evidence/replay-receipt.json')
 for p in Path('extracted/logs').glob('*'):z.write(p,'evidence/'+p.name)
 for p in Path('negative-controls').glob('*.log*'):z.write(p,'evidence/negative-'+p.name)
 z.write('negative-controls/results.json','evidence/negative-controls.json')
 assert not any(n.endswith(('.olean','.ilean','.ir')) for n in z.namelist())
Path('packet-receipt.json').write_text(json.dumps(dict(packet='edgepattern-r2-partial-source.zip',sha256=sha('edgepattern-r2-partial-source.zip'),source_only=True,formal_source_sha256=sourcehashes,all_formal_sources_and_replay_driver_identical_to_successful_fresh_replay=True),indent=2)+'\n')
print(json.dumps(dict(status='PARTIAL_ZERO_CREDIT',declarations=total,counts=counts,packet_bytes=Path('edgepattern-r2-partial-source.zip').stat().st_size)))
