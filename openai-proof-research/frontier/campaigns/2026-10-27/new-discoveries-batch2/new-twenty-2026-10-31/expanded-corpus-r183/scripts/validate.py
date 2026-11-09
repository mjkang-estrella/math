from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'results.json').read_text());res=json.loads((D/'reservation.json').read_text())
assert len(r)==20 and set(map(int,r))==set(res['ids'])
for i,o in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert sha(b)==o['provenance']['raw_sha256'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert o['credit']==0
 for f in o['source_artifacts']:assert sha((D/f['path']).read_bytes())==f['sha256']
assert json.loads((D/'outputs/promotion-fast8.json').read_text())['linear_extensions']==315031552
assert json.loads((D/'outputs/block-identity.json').read_text())['ordered_pairs']==3969
assert 'n=14' in (D/'logs/shuffle-final.log').read_text() and 'FAIL' not in (D/'logs/shuffle-final.log').read_text()
receipts=[json.loads(p.read_text())|{'receipt':str(p.relative_to(D))} for p in (D/'logs').glob('*.receipt.json')]
assert all(x['cap_reason'] is None for x in receipts)
# Failed compiler attempts are explicitly retained and not tests of the mathematical claim.
assert all(x['returncode']==0 for x in receipts if 'compile-shuffle.receipt' not in x['receipt'])
for name in ['SUMMARY.md','CANDIDATE.md','outputs/registry-screen.json']:assert (D/name).is_file()
manifest={str(p.relative_to(D)):{'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in D.rglob('*') if p.is_file() and p.name!='artifact-manifest.json'}
(D/'outputs/artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(D/'outputs/validation.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_reserved_ids':20,'raw_lines_hashes_checked':20,'source_hashes_checked':True,'all_logged_runs_finished':True,'watchdog_kills':0,'formal_claims':0,'result':'PASS','resource_receipts':receipts},indent=2)+'\n')
print('PASS: 20 reserved IDs, exact raw lines and hashes, source artifacts, numerical outputs, finished capped logs; no formal or accepted claims.')
