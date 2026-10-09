"""Verify provenance independently of the mathematical proof; --write seals artifacts."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[3]
source=root/'frontier/sources/i14_spectral_width'
experiment=root/'frontier/experiments/i14_spectral_width'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((source/'source-manifest.json').read_text())
tree=json.loads((root/'sources/preprints-tree.json').read_text())
assert tree.get('truncated') is False
entries={e['path']:e for e in tree['tree']}
for row in manifest['files']:
 p=root/row['local'];data=p.read_bytes()
 blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert sha(p)==row['sha256'] and blob==row['git_blob']
 # The complete inventory is rooted at preprints/.
 e=entries.get(row['path']) or entries.get(row['path'].removeprefix('preprints/'))
 assert e is not None and e['sha']==blob
for row in json.loads((source/'literature/manifest.json').read_text()):
 p=root.parent/row['file'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
seal=source/'artifact-manifest.json'
if '--write' in sys.argv:
 files=[root/'AGENTS.md',root/'sources/upstream.json',root/'sources/preprints-tree.json',root/'frontier/iterations/i14-sharp-spectral-width.md',root/'frontier/iterations/iteration14-spectral-width-r2-task.json']
 files += [p for folder in [source,experiment] for p in folder.rglob('*') if p.is_file() and p!=seal]
 seal.write_text(json.dumps({'files':[{'path':str(p.relative_to(root)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(set(files))]},indent=2)+'\n')
rows=json.loads(seal.read_text())['files']
for row in rows:
 p=root/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],row['path']
print(json.dumps({'status':'PASS','pinned_files':len(manifest['files']),'literature_files':4,'sealed_files':len(rows),'limitation':'Provenance and finite algebra only; independent mathematical review remains required.'}))
