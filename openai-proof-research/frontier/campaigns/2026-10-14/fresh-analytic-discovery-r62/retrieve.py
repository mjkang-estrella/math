"""Pinned source acquisition; writes only this owned packet's private directory."""
from pathlib import Path
import hashlib,json,urllib.request
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())
assert tree['truncated'] is False
terms=['The-entropy-rate-dimension-formula','The-curve-scaling-limit-of-half-plane-double-dimers','The-three-quarter']
rows=[]
for x in tree['tree']:
 if x['type']!='blob' or not x['path'].endswith(('.tex','.bib')) or not any(t in x['path'] for t in terms):continue
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path']
 data=urllib.request.urlopen(url).read();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert blob==x['sha']
 p=HERE/'private'/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 rows.append(dict(path=x['path'],local=str(p.relative_to(HERE)),url=url,git_blob=blob,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
(HERE/'source-receipts.json').write_text(json.dumps(dict(pin=PIN,canonical_tree_sha256=hashlib.sha256((ROOT/'sources/preprints-tree.json').read_bytes()).hexdigest(),files=rows),indent=2)+'\n')
print(len(rows))
