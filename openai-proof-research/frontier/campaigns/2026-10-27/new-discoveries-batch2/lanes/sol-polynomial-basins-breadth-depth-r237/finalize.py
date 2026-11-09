import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
B=L.parent.parent
guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
ledger=json.loads((L/'admin/ledger.json').read_text());prior=json.loads((L/'admin/prior-campaign-context.json').read_text())
assert [ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']]==[9,39,40]
provenance=dict(lane=str(L),timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='ordinary proof proposed; unaccepted; novelty uncleared',counts=dict(additional=9,total=39,next=40),authority='root alone accepts and counts',guard=dict(path=str(guard),sha256=h(guard),AS_bytes=512*1024**2,groupRSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),cap_raises=False),scientific_bindings='source-bindings.json',postread_checks='source-postread-checks.json',retrieval_receipts='retrieval-receipts.jsonl',administrative_snapshots='admin-snapshots.json',prior_context_keys=list(prior),history_screens=['history-4.json','history-12.json'],history_scope='immediate current-batch SUMMARY/discovery/SCOUTING; r231/r234 exact frozen scouting; prior administrative accepted/held/rejected context; not exhaustive historical sources',sources=dict(primary='https://cs.uwaterloo.ca/journals/JIS/VOL16/Borisov/borisov3.pdf',primary_sha256=h(L/'sources/original-borisov.pdf'),question='Question10 p4',first_public='arXiv:1301.0517v1 p2, 2013-01-03',journal_publication='2013-10-12',actual_followup='arXiv:1505.03237v1, 2015-05-13'),results=dict(main='universal obstruction, PROOF.md',routine='root-proposed dismal C26 bridge, routine-proof.md',breadth_families=8,novelty_cleared=0),limits=['No current public proof-registry head verification; inherited denials respected','No unavailable historical interval reopened','No global priority guarantee','No formalization, manuscript or child work'],forbidden_actions_performed=False)
(L/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
# Record final source originals/copies after all scientific use.
checks=[]
for r in json.loads((L/'source-bindings.json').read_text()):
 a,b=pathlib.Path(r['original']),pathlib.Path(r['copy']);ok=h(a)==h(b)==r['sha256'];assert ok
 checks.append(dict(original=str(a),copy=str(b),sha256=r['sha256'],unchanged=True))
(L/'source-postread-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
excluded={'final-manifest.json','verification-receipt.json'}
files=[p for p in L.rglob('*') if p.is_file() and p.name not in excluded]
manifest={str(p.relative_to(L)):dict(sha256=h(p),bytes=p.stat().st_size) for p in sorted(files)}
(L/'final-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(manifest_files=len(manifest),scientific_bindings=len(checks),counts=[9,39,40])))
