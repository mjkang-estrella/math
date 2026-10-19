#!/usr/bin/env python3
"""Read-only integrity verifier. An externally supplied manifest hash is mandatory.
No mathematical validity or gate verdict is verified by this program.
"""
import argparse, hashlib, json, os, pathlib, stat, sys

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def regular(p):
    st=p.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('not a single-link regular file: '+str(p))
    for a in p.parents:
        if a.is_symlink():raise ValueError('symlink ancestor: '+str(a))
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);ap.add_argument('--root',type=pathlib.Path,default=pathlib.Path(__file__).absolute().parent);ap.add_argument('--private',action='store_true');ap.add_argument('--context-root',type=pathlib.Path);a=ap.parse_args()
    root=a.root.absolute()
    if root.is_symlink():raise ValueError('root symlink')
    mp=root/'manifest.json';regular(mp)
    if len(a.anchor)!=64 or digest(mp)!=a.anchor:raise ValueError('external manifest anchor mismatch')
    m=json.loads(mp.read_text());expected=set()
    for rec in m['public']:
        name=rec['path'];p=pathlib.PurePosixPath(name)
        if p.is_absolute() or '..' in p.parts or name in expected:raise ValueError('unsafe/duplicate inventory')
        expected.add(name);fp=root/name;regular(fp)
        if fp.stat().st_size!=rec['bytes'] or digest(fp)!=rec['sha256']:raise ValueError('payload mismatch: '+name)
    actual={p.name for p in root.iterdir() if p.name not in ('private','manifest.json')}
    if actual!=expected:raise ValueError('public membership mismatch')
    for p in root.iterdir():
        if p.name=='private':
            if not p.is_dir() or p.is_symlink():raise ValueError('invalid private root')
        elif p.is_dir():raise ValueError('unexpected public directory')
    if a.private:
        expected_private={x['path'] for x in m['private_evidence']}
        actual_private=set()
        for dp,dirs,files in os.walk(root/'private',followlinks=False):
            for dn in dirs:
                if (pathlib.Path(dp)/dn).is_symlink():raise ValueError('private directory symlink')
            for fn in files:actual_private.add(str((pathlib.Path(dp)/fn).relative_to(root)))
        if expected_private!=actual_private:raise ValueError('private membership mismatch')
        for rec in m['private_evidence']:
            fp=root/rec['path'];regular(fp)
            if fp.stat().st_size!=rec['bytes'] or digest(fp)!=rec['sha256']:raise ValueError('private identity mismatch')
        rs=json.loads((root/'source-receipts.json').read_text())
        for rec in rs['records']:
            if not rec['success']:continue
            data=(root/rec['local']).read_bytes()
            blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            if blob!=rec['git_blob']:raise ValueError('Git blob mismatch')
    if a.context_root:
        for rec in json.loads((root/'context-receipts.json').read_text()):
            p=a.context_root/rec['path'];regular(p)
            if digest(p)!=rec['sha256']:raise ValueError('external context changed: '+rec['path'])
        tree=json.loads((a.context_root/'sources/preprints-tree.json').read_text())
        if len(tree['tree'])!=13223 or tree['truncated']:raise ValueError('not complete tree')
        blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
        for rec in json.loads((root/'source-receipts.json').read_text())['records']:
            if rec['success'] and blobs.get(rec['path'])!=rec['git_blob']:raise ValueError('canonical tree blob mismatch')
    print(json.dumps({'integrity':'verified','public_files':len(m['public']),'private_checked':a.private,'context_checked':bool(a.context_root),'mathematical_proof':False,'independent_gate':False}))
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,KeyError,TypeError,json.JSONDecodeError) as e:
        print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
