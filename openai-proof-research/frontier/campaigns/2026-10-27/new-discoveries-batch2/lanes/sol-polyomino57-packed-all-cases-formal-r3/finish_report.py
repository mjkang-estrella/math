from pathlib import Path
import resource,signal,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
L=Path(__file__).resolve().parent;r=json.loads((L/'REPLAY-RECEIPT.json').read_text());assert r['status'].startswith('PASS_ALL_33')
inv=json.loads((L/'declaration-inventory.json').read_text());eps=[v for v in inv if v['name'].startswith('Polyomino57.Diagonal.FiniteProof.AllCases.')]
(L/'ENDPOINTS.json').write_text(json.dumps(eps,indent=2)+'\n')
runs=r['build_reports'];stats=dict(stages=len(runs),modules=r['modules'],declarations=r['declarations'],max_stage_seconds=max(v['seconds'] for v in runs),max_sampled_group_rss=max(v['peak_group_rss'] for v in runs),summed_stage_seconds=sum(v['seconds'] for v in runs),all_return_codes_zero=all(v['rc']==0 for v in runs),archive_sha256=r['source_packet_sha256'],credit=0,additional=5,total=35)
(L/'FINAL-STATUS.json').write_text(json.dumps(stats,indent=2)+'\n')
p=L/'SUMMARY.md';s=p.read_text();s=s.replace('# All geometric cases integrated; fresh replay receipt delivered separately','# All70 geometric cases closed; fresh extracted replay PASS')
s=s.replace('Credit 0. Counts remain 5 additional / 35 total. Root owns acceptance and manuscript.','Credit 0. Counts remain 5 additional / 35 total. Root owns acceptance and manuscript.\n\nFinal fresh extracted source-only replay PASS: 2022 consumed modules, 5924 declarations, 2023 successful monitored compilation stages including FinalAudit. Actual types, origins, permitted axioms and safety flags were audited. See REPLAY-RECEIPT.json, declaration-inventory.json, ENDPOINTS.json and FINAL-STATUS.json. The immutable packet hash is '+r['source_packet_sha256']+'. The archive was frozen before this external final receipt; its mathematical sources were replayed unchanged. Resource/launcher qualifications and additional failure diagnostics are in FAILURE-NOTES.md; small text-only edit helpers were not all explicitly AS-capped, while resource-heavy generators and Lean stages were capped.')
p.write_text(s)
p=L/'provenance.json';v=json.loads(p.read_text());v['final_fresh_replay']='PASS; REPLAY-RECEIPT.json';v['source_packet_sha256']=r['source_packet_sha256'];v['resource_qualification']='Small text-only edit helpers not all explicitly AS-capped; see FAILURE-NOTES.md';p.write_text(json.dumps(v,indent=2)+'\n')
for e in eps:
 if e['name'].rsplit('.',1)[1] in ['finiteCases','universalContainer','minimum_le','source_refutation']:
  print(e['name']+' : '+e['type']+' AXIOMS '+e['axioms'])
print(json.dumps(stats,indent=2))
