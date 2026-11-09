from pathlib import Path
import json,hashlib,urllib.request,datetime
R=Path(__file__).resolve().parents[1];P=R.parents[3]
t=json.loads((P/'sources/preprints-tree.json').read_text());assert len(t['tree'])==13223 and not t['truncated']
families=['A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026','Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026']
rows=[]
for e in t['tree']:
 if any('/'+f+'/' in e['path'] for f in families) and e['path'].endswith('.tex'):
  url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
  b=urllib.request.urlopen(url,timeout=30).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert blob==e['sha'] and len(b)==e['size']
  d=R/'packet/private/sources'/e['path'];d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b)
  rows.append(dict(path=e['path'],url=url,size=len(b),git_blob_sha1=blob,sha256=hashlib.sha256(b).hexdigest(),acquired_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
(R/'packet/private/sources/authentication.json').write_text(json.dumps(rows,indent=2)+'\n');print('authenticated',len(rows),'source bodies')
