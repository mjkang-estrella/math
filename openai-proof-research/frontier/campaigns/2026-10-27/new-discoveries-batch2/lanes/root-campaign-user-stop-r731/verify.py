from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
for e in json.loads((P/'input-bindings.json').read_text()):
 b=Path(e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
m=json.loads((P/'manifest.json').read_text());assert {str(p.relative_to(P)) for p in P.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in m}
for e in m:
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
c=json.loads((P/'closeout.json').read_text());assert c['literal_record_reviews']==9133 and c['active_delegates']==0 and not c['automatic_continuation_authorized']
print('PASS: closeout payload, original root references, stop status and count boundary')
