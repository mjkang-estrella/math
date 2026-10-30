import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
receipts=[]
for n in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((L/n).read_bytes());bad=[p for p,h in j['files'].items() if not (L/p).is_file() or sha((L/p).read_bytes())!=h]
 assert not bad,(n,bad)
 receipts.append(dict(name=n,sha256=sha((L/n).read_bytes()),all_payload_hashes_pass=True))
assert not (L/'PROOF.md').exists()
manifest=json.loads((L/'finalmanifest.json').read_bytes());actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()};allowed=set(manifest['files'])|set(manifest['excluded_derived_outputs'])|{'finalmanifest.json'}
assert not actual-allowed,sorted(actual-allowed)
assert 'context-NEXT.md' not in json.loads((L/'scientific-freeze.json').read_bytes())['files']
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(guard.read_bytes())=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
j=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),result='PASS',receipts=receipts,complete_lane_file_coverage=True,guard_unchanged=True,source_resolution=False)
(L/'manifest-verification.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
