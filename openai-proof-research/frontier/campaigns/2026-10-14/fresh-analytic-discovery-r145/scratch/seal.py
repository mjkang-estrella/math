"""One-use own-root payload seal. No source/original manifest is inherited."""
from pathlib import Path
import fnmatch,hashlib,json,os
root=Path.cwd()/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r145'
envelopes={'FINAL.md','MANIFEST.json','REPORT.md'}
patterns=['*structural*r150*','*arithmetic*r114*','*structural*r151*','*arithmetic*r115*','*arithmetic*r116*']
assert not (root/'MANIFEST.json').exists(), 'already sealed'
assert (root/'FINAL.md').is_file() and (root/'REPORT.md').is_file()
rows=[]
for parent,dirs,files in os.walk(root,followlinks=False):
    for name in dirs+files:
        assert not any(fnmatch.fnmatchcase(name.lower(),p) for p in patterns), 'excluded peer component'
        assert not (Path(parent)/name).is_symlink(), 'symlink'
    for name in files:
        path=Path(parent)/name
        rel=path.relative_to(root).as_posix()
        if rel in envelopes: continue
        assert path.is_file(), 'nonregular file'
        data=path.read_bytes()
        rows.append({'path':rel,'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
rows.sort(key=lambda x:x['path'])
with (root/'MANIFEST.json').open('x') as out:
    out.write(json.dumps({'scope':'Exact own-root payload; three root envelopes excluded; no mathematical gate','files':rows},indent=2)+'\n')
print(json.dumps({'payload_files':len(rows),'outside_envelopes':3,'seal_writes':1}))
