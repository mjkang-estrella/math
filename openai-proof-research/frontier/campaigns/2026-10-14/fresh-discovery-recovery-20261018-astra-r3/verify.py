#!/usr/bin/env python3
"""Offline byte/provenance check. Does not certify mathematics or contribution."""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath

def sha(b):return hashlib.sha256(b).hexdigest()
def safe(s):
    p=PurePosixPath(s)
    if p.is_absolute() or '..' in p.parts or str(p)!=s:raise ValueError('unsafe path')
    return s

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--manifest-sha256',required=True);args=ap.parse_args()
    base=Path(__file__).resolve().parent
    mp=base/'MANIFEST.json'
    if mp.is_symlink() or not mp.is_file() or mp.stat().st_nlink!=1:raise ValueError('invalid manifest kind')
    raw=mp.read_bytes()
    if sha(raw)!=args.manifest_sha256:raise ValueError('external manifest anchor mismatch')
    m=json.loads(raw); expected={safe(x['path']):x for x in m['files']}
    if len(expected)!=len(m['files']):raise ValueError('duplicate file')
    found={};dirs=[]
    for root,dnames,fnames in os.walk(base,followlinks=False):
        for n in dnames:
            p=Path(root)/n
            if p.is_symlink():raise ValueError('symlink directory')
            dirs.append(p.relative_to(base).as_posix())
        for n in fnames:
            p=Path(root)/n;s=p.relative_to(base).as_posix();st=p.lstat()
            if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('nonregular or multiply linked payload')
            if s=='MANIFEST.json':continue
            b=p.read_bytes();found[s]={'path':s,'bytes':len(b),'sha256':sha(b)}
    if sorted(dirs)!=m['directories'] or found!=expected:raise ValueError('inventory or payload mismatch')
    tree=json.loads((base/'private/context/sources__preprints-tree.json').read_text())
    if tree['truncated']:raise ValueError('truncated canonical tree')
    canonical={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    rec=json.loads((base/'source-receipts.json').read_text())
    for r in rec:
        b=(base/safe(r['path'])).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if blob!=r['git_blob'] or blob!=canonical[r['upstream_path']] or sha(b)!=r['sha256']:raise ValueError('canonical source mismatch')
    primary=json.loads((base/'primary-receipts.json').read_text())
    for r in primary:
        if 'error' in r:continue
        p=base/safe(r['path'])
        if sha(p.read_bytes())!=r['sha256'] or sha(p.with_suffix('.txt').read_bytes())!=r['text_sha256']:raise ValueError('primary binding mismatch')
    a=json.loads((base/'scope-anchor.json').read_text())
    if sha((base/'scope-freeze.md').read_bytes())!=a['scope_sha256']:raise ValueError('scope mismatch')
    print(json.dumps({'status':'INTEGRITY_PASS_ONLY','files':len(found),'canonical_blobs':len(rec),'primary_pairs':sum('error' not in r for r in primary),'mathematical_status':'FULL_T188U_UNRESOLVED_NO_NOMINEE'},sort_keys=True))
if __name__=='__main__':main()
