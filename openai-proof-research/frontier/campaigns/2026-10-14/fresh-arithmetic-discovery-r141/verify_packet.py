"""Read-only byte verifier. Explicit detached anchors are mandatory; no mathematical verdict."""
import argparse, hashlib, json, sys
from pathlib import Path, PurePosixPath

def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',required=True)
    for n in ('final','manifest','report'):ap.add_argument('--'+n+'-sha256',required=True)
    a=ap.parse_args(); root=Path(a.root).resolve()
    expected={'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}
    for name,h in expected.items():
        if len(h)!=64 or any(c not in '0123456789abcdef' for c in h):raise ValueError('Invalid explicit anchor: '+name)
        p=root/name
        if p.is_symlink() or digest(p)!=h:raise ValueError('Detached anchor mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    if m['schema']!='r141-exact-selection-v1':raise ValueError('Schema mismatch')
    names=set()
    for row in m['files']:
        name=row['path']; pp=PurePosixPath(name)
        if pp.is_absolute() or '..' in pp.parts or str(pp)!=name or name in names:raise ValueError('Unsafe/duplicate member')
        p=root.joinpath(*pp.parts)
        if p.is_symlink() or not p.is_file() or root not in p.resolve().parents:raise ValueError('Unsafe member '+name)
        if p.stat().st_size!=row['bytes'] or digest(p)!=row['sha256']:raise ValueError('Member mismatch: '+name)
        names.add(name)
    omitted={'MANIFEST.json','REPORT.md','ANCHORS.json'}
    if set(m['detached'])!=omitted or names & omitted:raise ValueError('Detached set mismatch')
    actual=set()
    for p in root.rglob('*'):
        if p.is_symlink():raise ValueError('Symlink present')
        if p.is_file():actual.add(p.relative_to(root).as_posix())
    if actual-omitted!=names:raise ValueError('Exact membership mismatch')
    if 'FINAL.md' not in names:raise ValueError('FINAL missing from selection')
    print(json.dumps({'artifact_bytes':'consistent','selected_files':len(names),'mathematical_verdict':None}))

if __name__=='__main__':
    try:main()
    except Exception as exc:
        print(str(exc),file=sys.stderr);sys.exit(1)
