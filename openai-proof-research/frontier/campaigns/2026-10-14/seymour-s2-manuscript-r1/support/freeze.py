"""Deliberately freeze an inspected payload; not an acceptance gate. MIT."""
from pathlib import Path
import hashlib,json,zipfile
R=Path(__file__).resolve().parents[1]
if json.loads((R/'formal-scope.json').read_text())['status'].startswith('PENDING'):raise RuntimeError('Final formal coverage required before freeze')
paths=json.loads((R/'public-files.json').read_text())
assert len(paths)==len(set(paths)) and 'public-manifest.json' not in paths
records=[]
for name in sorted(paths):
    p=R/name
    assert p.is_file() and not p.is_symlink(),name
    b=p.read_bytes();records.append({'path':name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(R/'public-manifest.json').write_text(json.dumps({'schema':1,'files':records,'meaning':'Byte consistency only, not proof or acceptance. Third-party source files and PDFs excluded.'},indent=2)+'\n')
with zipfile.ZipFile(R/'seymour-s2-public.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
    for name in sorted(paths+['public-manifest.json']):
        info=zipfile.ZipInfo(name,date_time=(2026,10,16,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
        z.writestr(info,(R/name).read_bytes())
local=[]
for p in sorted(R.rglob('*')):
    rel=p.relative_to(R).as_posix()
    if p.is_file() and not rel.startswith('tmp/') and rel not in {'output-manifest.json','SHA256SUMS'}:
        b=p.read_bytes();local.append({'path':rel,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(R/'output-manifest.json').write_text(json.dumps({'files':local},indent=2)+'\n')
(R/'SHA256SUMS').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in local)+hashlib.sha256((R/'output-manifest.json').read_bytes()).hexdigest()+'  output-manifest.json\n')
print(json.dumps({name:hashlib.sha256((R/name).read_bytes()).hexdigest() for name in ['public-manifest.json','seymour-s2-public.zip','output-manifest.json','SHA256SUMS']},indent=2))
