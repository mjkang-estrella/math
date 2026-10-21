#!/usr/bin/env python3
"""Read-only selected-membership verifier; three anchors must arrive independently."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b): return hashlib.sha256(b).hexdigest()
def members(root):
    out={}
    for base,dirs,files in os.walk(root,topdown=True,followlinks=False):
        for name in dirs+files:
            p=Path(base)/name; st=p.lstat()
            if stat.S_ISLNK(st.st_mode): raise ValueError('symlink: '+str(p.relative_to(root)))
            if not (stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode)): raise ValueError('nonregular member')
            if stat.S_ISREG(st.st_mode) and st.st_nlink!=1: raise ValueError('hardlinked member')
        for name in files:
            p=Path(base)/name; rel=p.relative_to(root).as_posix()
            if rel in ENVELOPES: continue
            b=p.read_bytes();out[rel]={'size':len(b),'sha256':sha(b)}
    return out

def verify(root,anchors):
    root=Path(root)
    if root.is_symlink() or not root.is_dir(): raise ValueError('invalid root')
    for name in ENVELOPES:
        p=root/name; st=p.lstat()
        if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1: raise ValueError('invalid envelope: '+name)
        expected=anchors[name]
        if len(expected)!=64 or any(c not in '0123456789abcdef' for c in expected): raise ValueError('invalid external anchor')
        if sha(p.read_bytes())!=expected: raise ValueError('envelope anchor mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    if m['schema']!='r155-selected-membership-v1' or set(m['outside_envelopes'])!=ENVELOPES: raise ValueError('manifest contract')
    expected={}
    for x in m['files']:
        q=x['path'];p=PurePosixPath(q)
        if p.is_absolute() or '..' in p.parts or p.as_posix()!=q or q in ENVELOPES or q in expected: raise ValueError('unsafe/duplicate manifest path')
        expected[q]={'size':x['size'],'sha256':x['sha256']}
    actual=members(root)
    if set(actual)!=set(expected): raise ValueError('payload membership mismatch')
    for q in expected:
        if expected[q]!=actual[q]: raise ValueError('payload bytes mismatch: '+q)
    return {'files':len(actual),'bytes':sum(x['size'] for x in actual.values()),'meaning':'artifact membership and bytes only'}

if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('root');a.add_argument('--final-sha256',required=True);a.add_argument('--manifest-sha256',required=True);a.add_argument('--report-sha256',required=True);x=a.parse_args()
    print(json.dumps(verify(x.root,{'FINAL.md':x.final_sha256,'MANIFEST.json':x.manifest_sha256,'REPORT.md':x.report_sha256}),sort_keys=True))
