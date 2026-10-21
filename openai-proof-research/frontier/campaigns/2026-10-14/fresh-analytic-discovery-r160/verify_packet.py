"""Read-only byte/membership verifier; external anchors are required. Not a math gate."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,sys
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(b):return hashlib.sha256(b).hexdigest()
def verify(root,anchors):
    root=Path(root)
    for name,h in anchors.items():
        p=root/name
        if p.is_symlink() or not p.is_file() or digest(p.read_bytes())!=h:
            raise ValueError('detached envelope mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_bytes())
    if m.get('schema')!='r160.exact-files.v1':raise ValueError('wrong schema')
    wanted={}
    for entry in m['files']:
        name=entry['path'];p=PurePosixPath(name)
        if p.is_absolute() or '..' in p.parts or str(p)!=name or name in ENVELOPES or name in wanted:
            raise ValueError('unsafe/duplicate member')
        wanted[name]=entry
    actual={}
    for p in root.rglob('*'):
        if p.is_symlink():raise ValueError('symlink rejected')
        if p.is_file():
            name=p.relative_to(root).as_posix()
            if name not in ENVELOPES:actual[name]=p
        elif not p.is_dir():raise ValueError('special node rejected')
    if set(actual)!=set(wanted):raise ValueError('membership mismatch')
    total=0
    for name,p in actual.items():
        b=p.read_bytes();e=wanted[name]
        if len(b)!=e['bytes'] or digest(b)!=e['sha256']:raise ValueError('payload mismatch: '+name)
        total+=len(b)
    return {'files':len(actual),'bytes':total,'scope':'regular-file bytes and membership only; no mathematical verdict'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',required=True)
    for key in ['final','manifest','report']:p.add_argument('--'+key+'-sha',required=True)
    a=p.parse_args()
    try:
        print(json.dumps(verify(a.root,{'FINAL.md':a.final_sha,'MANIFEST.json':a.manifest_sha,'REPORT.md':a.report_sha}),sort_keys=True))
    except Exception as e:
        print(str(e),file=sys.stderr);sys.exit(1)
