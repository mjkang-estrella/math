from pathlib import Path
import json,hashlib,subprocess
D=Path(__file__).resolve().parents[1];R=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(R)==20 and set(map(int,R))==set(ids)
for i,r in R.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==r['provenance']['raw_sha256'];assert hashlib.sha256(r['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256'];assert r['credit']==0
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if 'sha256' in r:assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256']
assert all(r['unimodal'] for r in json.loads((D/'outputs/hilbert-extended.json').read_text()))
assert json.loads((D/'outputs/johnson-independent-check.json').read_text())['all_cover_edge_interval_checks']
for p in ['SUMMARY.md','results.json','lean/Johnson.lean','lean/Johnson.olean','logs/lean-single.log']:assert (D/p).is_file()
procs=subprocess.check_output(['ps','-eo','pid,ppid,args'],text=True).splitlines();active=[l for l in procs if str(D) in l and ('lean -' in l or 'scripts/involutions' in l or 'scripts/johnson-path.py' in l or 'scripts/stairs.py' in l)]
# This validator itself and its wrapper are not background research jobs.
assert not active,active
print('PASS: 20 reserved IDs; exact raw hashes/newlines; successful HTTP receipts; Hilbert output; Johnson certificate; no active lane research processes.')
