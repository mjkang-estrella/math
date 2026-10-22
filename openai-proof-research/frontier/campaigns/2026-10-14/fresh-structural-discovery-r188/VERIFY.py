#!/usr/bin/env python3
"""Read-only artifact verification; no mathematical gate. Supply detached anchors."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath

def digest(b):
    return hashlib.sha256(b).hexdigest()

def safe(root, name):
    pp=PurePosixPath(name)
    if pp.is_absolute() or '..' in pp.parts:
        raise ValueError('unsafe relative path')
    p=root.joinpath(*pp.parts)
    if p.is_symlink() or root.resolve() not in p.resolve().parents:
        raise ValueError('unsafe target')
    return p

def verify(root, anchors, originals=None):
    for name, expected in anchors.items():
        if digest(safe(root,name).read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: '+name)
    manifest=json.loads((root/'private/MANIFEST.json').read_bytes())
    names=set()
    for row in manifest['files']:
        name=row['path']
        if name in names:
            raise ValueError('duplicate payload')
        names.add(name)
        b=safe(root,name).read_bytes()
        if len(b)!=row['bytes'] or digest(b)!=row['sha256']:
            raise ValueError('payload mismatch: '+name)
    if 'FINAL.md' not in names or {'REPORT.md','private/MANIFEST.json','ANCHORS.json'} & names:
        raise ValueError('detachment failure')
    if originals is not None:
        bindings=json.loads((root/'private/original-bindings.json').read_bytes())
        for row in bindings:
            p=safe(originals,row['path'])
            with p.open('rb') as f:
                f.seek(row['start']); b=f.read(row['end']-row['start'])
            if len(b)!=row['end']-row['start'] or digest(b)!=row['sha256']:
                raise ValueError('original span mismatch: '+row['path'])
            if safe(root,row['copy']).read_bytes()!=b:
                raise ValueError('copied span mismatch: '+row['copy'])
        tb=(originals/'sources/preprints-tree.json').read_bytes()
        if len(tb)!=4858136 or digest(tb)!='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b':
            raise ValueError('tree metadata mismatch')
        tree=json.loads(tb)['tree']
        if len(tree)!=13223:
            raise ValueError('tree count mismatch')
        bypath={x['path']:x for x in tree}
        auth=json.loads((root/'private/source-auth.json').read_bytes())
        family='preprints/The-Grothendieck-homotopy-hypothesis-via-elementary-expansions-September-24-2026/'
        expected={x['path'] for x in tree if x['type']=='blob' and x['path'].casefold().startswith(family.casefold())}
        if expected!={x['path'] for x in auth}:
            raise ValueError('canonical blob selection mismatch')
        for row in auth:
            rel='private/source/'+row['path'].split('September-24-2026/',1)[1]
            b=safe(root,rel).read_bytes()
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            if blob!=row['git_blob'] or blob!=bypath[row['path']]['sha'] or len(b)!=bypath[row['path']]['size'] or digest(b)!=row['sha256']:
                raise ValueError('source binding mismatch')
        for row in json.loads((root/'private/primary-read-extents.json').read_bytes()):
            b=safe(root,row['copy']).read_bytes()[row['start']:row['end']]
            if digest(b)!=row['sha256']:
                raise ValueError('primary extent mismatch')
        print('Matched',len(bindings),'exact original spans and',len(auth),'canonical source blobs.')
    print('Matched artifact verification on',len(names),'payload files; no mathematical gate.')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--final',required=True)
    ap.add_argument('--manifest',required=True)
    ap.add_argument('--report',required=True)
    ap.add_argument('--originals',type=Path)
    a=ap.parse_args()
    try:
        verify(a.root,{'FINAL.md':a.final,'private/MANIFEST.json':a.manifest,'REPORT.md':a.report},a.originals)
    except (ValueError,OSError,KeyError,json.JSONDecodeError) as e:
        raise SystemExit(str(e))
