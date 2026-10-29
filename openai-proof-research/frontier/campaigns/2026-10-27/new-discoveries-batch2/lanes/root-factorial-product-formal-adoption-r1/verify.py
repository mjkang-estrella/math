import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent
s=r.parent/'sol-factorial-product-source-formal-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
final=json.loads((s/'FINAL-RECEIPT.json').read_text())
for n,h in final['receipt_and_artifact_hashes'].items():assert sha(s/n)==h,n
m=json.loads((s/'manifest.json').read_text())
for n,h in m.items():assert sha(s/n)==h,n
paths=set(m)|set(final['receipt_and_artifact_hashes'])|{'FINAL-RECEIPT.json','delivery-manifest.json'}
(r/'component-freeze.json').write_text(json.dumps({'root':str(s),'files':{n:sha(s/n) for n in sorted(paths)}},indent=2)+'\n')
out={'status':'MANIFEST_AND_RECEIPT_HASHES_PASS','payload_entries':len(m),'frozen_entries':len(paths),'archive_sha256':sha(s/'source-only.zip'),'credit':0,'counts':[8,38]}
(r/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
