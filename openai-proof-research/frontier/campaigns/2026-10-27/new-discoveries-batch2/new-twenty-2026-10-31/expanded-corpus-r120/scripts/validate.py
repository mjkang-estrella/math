from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();X=json.loads((D/'results.json').read_text());R=json.loads((D/'reservation.json').read_text())
assert len(X)==20 and set(map(int,X))==set(R['ids'])
inv=D.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301';mp=inv/'manifest.json';manifest=json.loads(mp.read_bytes());bound={str((inv/f['path']).resolve()):f['sha256'] for f in manifest['files']}
for k,x in X.items():
 raw=(D/f'raw/{k}.jsonl').read_bytes();p=x['provenance'];assert raw.endswith(b'\n') and sha(raw)==p['raw_sha256'];assert sha(x['statement'].encode())==p['statement_utf8_sha256'];assert bound[p['chunk']]==p['chunk_sha256'];assert not x['accepted'] and x['discovery_credit']==0
 for src in x['primary_source_bodies']:assert sha((D/src['path']).read_bytes())==src['sha256']
for stage in ['fresh-build','fresh-leanchecker2','fresh-audit']:
 r=json.loads((D/f'logs/{stage}.receipt.json').read_text());assert r['returncode']==0 and r['cap_reason'] is None
assert 'audited 81 local declarations' in (D/'logs/fresh-audit.log').read_text();assert 'declarations with non-allowed axioms: 0' in (D/'logs/fresh-audit.log').read_text()
for n in ['Code.lean','Audit.lean']:assert (D/'lean'/n).read_bytes()==(D/'fresh-packet'/n).read_bytes()
s=(D/'lean/Code.lean').read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',s)
package=json.loads((D/'outputs/package.json').read_text());assert package['sha256']==sha((D/'355525-lean-source.zip').read_bytes())
# Numerical summary only from complete per-process logs, with no invented coverage.
num={}
for p in (D/'logs').glob('*.log'):
 if p.stem.startswith(('delta-p','influence-')) or p.stem=='egz':
  try:num[p.stem]=[json.loads(l) for l in p.read_text().splitlines() if l.startswith('{')]
  except json.JSONDecodeError:pass
(D/'outputs/numerical-summary.json').write_text(json.dumps(num,indent=2)+'\n')
receipt={'results_entries':20,'ids_match_reservation':True,'raw_lines_and_statements_hash_verified':True,'source_body_hashes_verified':True,'chunk_hashes_match_inventory_manifest':True,'inventory_manifest_sha256':sha(mp.read_bytes()),'strict_replay_and_checker_and_audit':'PASS','local_declarations_audited':81,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'archive_sha256':package['sha256'],'accepted_credit':0}
(D/'outputs/validation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))