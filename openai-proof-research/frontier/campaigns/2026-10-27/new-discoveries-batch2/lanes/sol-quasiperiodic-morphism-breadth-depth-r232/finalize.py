import pathlib,json,hashlib,time
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=L/'SCOUTING.md';t=p.read_text().replace('Im–Liu–Xu,','Liu–Oki–Xu,').replace('22Oct2026 updated version (first5Sep2026)','29Oct2026 updated version (first5Sep2026)');p.write_text(t)
admin={name:json.loads((L/'administrative'/name).read_text()) for name in ['ledger.json','prior-campaign-context.json']}
ledger=admin['ledger.json'];assert (ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])==(9,39,40)
print('Administrative snapshots reconciled:',[(k,type(v).__name__,len(v)) for k,v in admin.items()])
bindings=json.loads((L/'frozenbindings.json').read_text())
for row in bindings:
 assert h(pathlib.Path(row['original']))==h(pathlib.Path(row['copy']))==row['sha256']
retrieval=[json.loads(x) for x in (L/'retrieval.jsonl').read_text().splitlines()]
for row in retrieval:
 if 'sha256' in row:assert h(pathlib.Path(row['file']))==row['sha256']
source_after=[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':h(p)} for root in ['primary','frozen'] for p in sorted((L/root).rglob('*')) if p.is_file()]
(L/'source-after.json').write_text(json.dumps(source_after,indent=2))
provenance={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'status':'No nomination; full conjecture unresolved','credit_requested':0,'counts_context':[9,39,40],'frozen_bindings':'frozenbindings.json','new_retrieval_receipts':'retrieval.jsonl','new_arxiv_pdfs':13,'primary_pdf_freeze':'receipt SHA256 and chmod0444 before pdftotext/scientific reads','after_verification':'source-after.json','history_files':len(json.loads((L/'history-bindings.json').read_text())),'history_freeze_limit':'Pre/post hash references, not immutable copies; native unfrozen helper/catalogue reads disclosed in FAILURES.md','current_registry':'Not obtained; denied routes not retried','proof_status':'No full candidate; no PROOF.md','resource_caps':{'AS_and_group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230},'forbidden_actions':False}
(L/'provenance.json').write_text(json.dumps(provenance,indent=2))
excluded={'finalmanifest.json','verification-receipt.json'}
manifest=[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':h(p)} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
(L/'finalmanifest.json').write_text(json.dumps(manifest,indent=2));print('Manifest entries',len(manifest))
