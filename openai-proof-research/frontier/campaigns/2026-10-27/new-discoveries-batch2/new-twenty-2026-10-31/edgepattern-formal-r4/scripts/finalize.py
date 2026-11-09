from pathlib import Path
import hashlib,json,re,collections,zipfile,shutil
r=Path(__file__).resolve().parents[1]; x=r/'extracted'
def put(p,v): p.write_text(json.dumps(v,indent=2)+'\n')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
replay=json.loads((x/'replay-receipt.json').read_text());neg=json.loads((x/'negative-results.json').read_text())
assert replay['passed'] and neg['passed']
for rel,h in replay['formal_source_sha256'].items(): assert sha(r/rel)==h
before=json.loads((r/'inputs-before.json').read_text());after={p:sha(Path(p)) for p in before};assert before==after
put(r/'inputs-after.json',after)
for p in (r.parent/'edgepattern-formal-r3/formal').glob('*.lean'):assert p.read_bytes()==(r/'formal'/p.name).read_bytes()
s=(x/'logs/replay-AuditR4.log').read_text(); counts=collections.Counter(re.findall(r'^MODULE (\S+)',s,re.M))
flags=re.findall(r'^AUDIT_FORBIDDEN_SAFETY (\S+)',s,re.M);axs=re.findall(r'^AUDIT_FORBIDDEN_AXIOM (.*)',s,re.M)
audit={'local_declarations':sum(counts.values()),'counts_by_module':dict(sorted(counts.items())),'total_expression_nodes':int(re.search(r'TOTAL_EXPR_NODES (\d+)',s)[1]),'safety_violations':flags,'forbidden_axioms':axs,'all_axioms_allowlisted':not axs,'audit_policy_pass':not flags and not axs,'log':'evidence/logs/replay-AuditR4.log','live_lane_log':'extracted/logs/replay-AuditR4.log','types_and_bodies':'complete expression DAG; opaque values requested with allowOpaque true'}
put(r/'audit-findings.json',audit)
for name in ['replay-receipt.json','negative-results.json']:shutil.copyfile(x/name,r/name)
receipts=[json.loads(p.read_text()) for p in (x/'logs').glob('*.receipt.json')]
verification={'lean_version':(x/'logs/version.log').read_text().strip(),'fresh_strict_replay':replay['passed'],'leanchecker_modules':sum(c['name'].startswith('leanchecker-') for c in replay['checks']),'compiled_modules':sum(c['name'].startswith('replay-') for c in replay['checks']),'negative_controls':neg['passed'],'audit_executed':True,'audit_policy_pass':audit['audit_policy_pass'],'policy_violations':flags,'forbidden_axioms':axs,'input_hashes_unchanged':True,'inherited_modules_byte_identical':266,'peak_sampled_private_rss_bytes':max(c['peak_sampled_private_rss_bytes'] for c in receipts),'max_wall_seconds':max(c['elapsed_seconds'] for c in receipts),'resource_kills':[c for c in receipts if c['killed']],'processes_sequential':True,'development_log_retention_complete':False,'unconditional_endpoint_proved':False}
put(r/'verification.json',verification)
old=json.loads((r/'inputs/edgepattern-formal-r3/results.json').read_text())['342414']
old.update(status='PARTIAL_ZERO_CREDIT',credit=0,root_accepted=False,refutation_proved=False,unconditional_endpoint=None,classification_proved=False,universal_tree_bound_proved=False,all_266_inherited_modules_byte_identical=True,inputs_unchanged=True,packet='edgepattern-r4-partial-source.zip',verification='verification.json',declarations={'total_including_generated':sum(counts.values()),'by_module':dict(sorted(counts.items()))},audit_policy_pass=audit['audit_policy_pass'],audit_safety_violations=flags,development_log_retention_complete=False)
old['new_proved_endpoints']={
'EdgePattern.TreeModelsR4.mem_children':'y ∈ children T x p ↔ T.graph.Adj x y ∧ y ≠ p',
'EdgePattern.TreeModelsR4.root_degrees':'TreeFamily T 3 2 → (T.graph.neighborSet T.left).ncard = 3 ∧ (T.graph.neighborSet T.right).ncard = 3',
'EdgePattern.TreeModelsR4.children_card':'T.graph.Adj x p → (children T x p).card + 1 = (T.graph.neighborSet x).ncard',
'EdgePattern.TreeModelsR4.root_children_card':'TreeFamily T 3 2 → (children T T.left T.right).card = 2 ∧ (children T T.right T.left).card = 2',
'EdgePattern.TreeModelsR4.children_card_le':'TreeFamily T 3 2 → T.graph.Adj x p → (children T x p).card ≤ 2',
'EdgePattern.TreeModelsR4.depth_coverage':'TreeFamily T 3 2 → x = T.left ∨ x = T.right ∨ T.graph.Adj x T.left ∨ T.graph.Adj x T.right ∨ (∃ p, T.graph.Adj x p ∧ T.graph.Adj p T.left) ∨ (∃ p, T.graph.Adj x p ∧ T.graph.Adj p T.right)',
'EdgePattern.TreeModelsR4.no_triangle':'T.graph.IsAcyclic → T.graph.Adj x y → T.graph.Adj y z → ¬ T.graph.Adj x z',
'EdgePattern.TreeModelsR4.root_children_disjoint':'TreeFamily T 3 2 → Disjoint (children T T.left T.right) (children T T.right T.left)',
'EdgePattern.TreeModelsR4.common_neighbor_unique':'T.graph.IsAcyclic → x ≠ y → T.graph.Adj x a → T.graph.Adj a y → T.graph.Adj x b → T.graph.Adj b y → a = b'}
old['new_endpoint_universes']='All StructureR4 results quantify over W : Type u, for arbitrary u. Fintype W is required except for no_triangle and common_neighbor_unique.'
put(r/'results.json',{'342414':old})
p=r/'SUMMARY.md';p.write_text(p.read_text()+f'\nFinal validation: strict fresh rebuild and leanchecker completed on {verification["compiled_modules"]} modules. All eight false-statement controls and existing-object refusal passed. The full audit inventoried {sum(counts.values())} declarations and {audit["total_expression_nodes"]} expression nodes, with one inherited generated unsafe helper and no forbidden axioms. Audit policy therefore does not pass. Source hashes are unchanged. See verification.json for resource maxima.\n')
# Final portable archive: sources plus complete final evidence, no compiled objects.
files=list((r/'formal').glob('*.lean'))+[r/'scripts'/n for n in ['replay.py','watchdog.py','negative.py','modules.json']]+list((r/'negative-controls').glob('*.lean'))+[r/n for n in ['SUMMARY.md','GAPS.md','REPRODUCE.md','statement-correspondence.md','inputs-before.json','inputs-after.json','copy-receipt.json','results.json','verification.json','audit-findings.json','development-history.json']]
with zipfile.ZipFile(r/'edgepattern-r4-partial-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files):z.write(p,p.relative_to(r))
 for p in sorted((x/'logs').glob('*')):z.write(p,Path('evidence/logs')/p.name)
 for n in ['replay-receipt.json','negative-results.json','replay-driver.log','negative-driver.log']:z.write(x/n,Path('evidence')/n)
with zipfile.ZipFile(r/'edgepattern-r4-partial-source.zip') as z:
 assert not any('.olean' in Path(n).suffixes for n in z.namelist())
put(r/'packet-receipt.json',{'sha256':sha(r/'edgepattern-r4-partial-source.zip'),'source_only':True,'endpoint':'partial; no unconditional refutation','fresh_formal_source_hashes_match_archive_sources':True,'final_evidence_included':True})
print(json.dumps(verification,indent=2))
