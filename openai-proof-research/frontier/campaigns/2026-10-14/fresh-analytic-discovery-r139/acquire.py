from pathlib import Path
import json,hashlib,urllib.request
R=Path(__file__).resolve().parent
P=R.parents[3]
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads((P/'sources/preprints-tree.json').read_bytes())
ledger=[]
for e in tree['tree']:
 if 'Sharp-One-Third-Stability-of-Brenier-Maps-' not in e['path'] or not e['path'].endswith(('.tex','.bib','README.md')):continue
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/'+e['path']
 b=urllib.request.urlopen(url,timeout=40).read()
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and sha==e['sha']
 dest=R/'private/source'/e['path'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 ledger.append(dict(path=e['path'],url=url,size=len(b),git_blob=sha,sha256=hashlib.sha256(b).hexdigest(),local=str(dest.relative_to(R)),read_extent='pending'))
(R/'source-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
print('authenticated',len(ledger),'source text files')
