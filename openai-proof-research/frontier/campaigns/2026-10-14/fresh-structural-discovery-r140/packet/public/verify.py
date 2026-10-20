#!/usr/bin/env python3
# Original code, MIT. Read-only local artifact verifier; not a mathematical gate.
import argparse,hashlib,json,re
from pathlib import Path

def sha(b):return hashlib.sha256(b).hexdigest()
def checked(p,want):
    if p.is_symlink() or not p.is_file():raise ValueError('missing/symlink: '+str(p))
    b=p.read_bytes()
    if sha(b)!=want:raise ValueError('SHA256 mismatch: '+str(p))
    return b
def inventory(root):
    rows=[]
    for top in ['packet','work']:
        p=root/top
        if not p.is_dir() or p.is_symlink():raise ValueError('bad payload root')
        for f in [p]+sorted(p.rglob('*')):
            if f.is_symlink():raise ValueError('symlink in payload')
            rel=f.relative_to(root).as_posix()
            if f.is_dir():rows.append(dict(path=rel,kind='directory'))
            elif f.is_file():
                b=f.read_bytes();rows.append(dict(path=rel,kind='file',size=len(b),sha256=sha(b)))
            else:raise ValueError('nonregular payload entry')
    return sorted(rows,key=lambda x:x['path'])
def verify(root,ma,ra,fa):
    for h in [ma,ra,fa]:
        if not re.fullmatch('[0-9a-f]{64}',h):raise ValueError('need complete detached anchors')
    mb=checked(root/'MANIFEST.json',ma);rb=checked(root/'outsideREPORT.md',ra);fb=checked(root/'FINAL.json',fa)
    manifest=json.loads(mb);final=json.loads(fb)
    if manifest['entries']!=inventory(root):raise ValueError('exact payload inventory mismatch')
    if final['manifest_sha256']!=ma or final['outside_report_sha256']!=ra:raise ValueError('final binding mismatch')
    scope=checked(root/'packet/public/frozen-scope.md',final['scope_sha256'])
    fr=json.loads((root/'packet/private/scope-freeze.json').read_text())
    if fr['sha256']!=sha(scope):raise ValueError('scope-freeze mismatch')
    tp=root/'packet/private/context/sources/preprints-tree.json'
    tb=checked(tp,'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b')
    tree=json.loads(tb)
    if tree['truncated'] or len(tree['tree'])!=13223:raise ValueError('wrong tree')
    by={e['path']:e for e in tree['tree']}
    auth=json.loads((root/'packet/private/sources/authentication.json').read_text())
    for a in auth:
        path=a['path']
        if path not in by or '..' in Path(path).parts or Path(path).is_absolute():raise ValueError('bad source path')
        b=checked(root/'packet/private/sources'/path,a['sha256']);e=by[path]
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if len(b)!=e['size'] or blob!=e['sha'] or blob!=a['git_blob_sha1'] or len(b)!=a['size']:raise ValueError('source identity mismatch')
        if 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' not in a['url']:raise ValueError('wrong pin URL')
    acq=json.loads((root/'packet/private/primary/acquisition.json').read_text())
    for a in acq:
        checked(root/'packet/private/primary'/(a['name']+'.pdf'),a['sha256'])
        checked(root/'packet/private/primary'/(a['name']+'.txt'),a['text_sha256'])
    return dict(status='ARTIFACT_IDENTITIES_ONLY',payload_entries=len(manifest['entries']),payload_files=sum(x['kind']=='file' for x in manifest['entries']),pinned_sources=len(auth),primary_pairs=len(acq),mathematical_verdict=None)
if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--root',type=Path,required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--report-sha256',required=True)
    p.add_argument('--final-sha256',required=True)
    a=p.parse_args()
    try:print(json.dumps(verify(a.root.resolve(),a.manifest_sha256,a.report_sha256,a.final_sha256),sort_keys=True))
    except Exception as e:raise SystemExit('VERIFY FAILED: '+str(e))
