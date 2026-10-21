#!/usr/bin/env python3
"""Read-only exact-membership verification. All three detached hashes are required."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat, sys
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b): return hashlib.sha256(b).hexdigest()
def checked_name(s):
    p=PurePosixPath(s)
    if not isinstance(s,str) or p.is_absolute() or '..' in p.parts or str(p)!=s or s=='.':
        raise ValueError('unsafe manifest path')
    return s

def verify(root, anchors):
    if not root.is_dir() or root.is_symlink(): raise ValueError('invalid root')
    for name, expected in anchors.items():
        p=root/name;st=p.lstat()
        if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1: raise ValueError('nonregular envelope '+name)
        if sha(p.read_bytes())!=expected: raise ValueError('detached hash mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    if m['schema']!=1: raise ValueError('manifest schema')
    entries=m['payload'];expected_files={};expected_dirs=set()
    for e in entries:
        s=checked_name(e['path'])
        if s in expected_files or s in ENVELOPES: raise ValueError('duplicate or envelope payload')
        expected_files[s]=e
    for s in m['directories']:
        s=checked_name(s)
        if s in expected_dirs: raise ValueError('duplicate directory')
        expected_dirs.add(s)
    files=set();dirs=set()
    for base, dn, fn in os.walk(root,topdown=True,followlinks=False):
        b=Path(base)
        for n in dn:
            p=b/n;st=p.lstat()
            if not stat.S_ISDIR(st.st_mode): raise ValueError('nonregular directory')
            dirs.add(p.relative_to(root).as_posix())
        for n in fn:
            p=b/n;st=p.lstat();rel=p.relative_to(root).as_posix()
            if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1: raise ValueError('nonregular/multiply-linked file '+rel)
            files.add(rel)
    if files!=set(expected_files)|ENVELOPES: raise ValueError('file membership mismatch')
    if dirs!=expected_dirs: raise ValueError('directory membership mismatch')
    for rel,e in expected_files.items():
        b=(root/rel).read_bytes()
        if len(b)!=e['size'] or sha(b)!=e['sha256']: raise ValueError('payload mismatch: '+rel)
    return {'artifact_verification':'pass','payloads':len(entries),'directories':len(dirs),'outside_envelopes':3,'mathematical_gate':False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('root',type=Path)
    p.add_argument('--final-sha256',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    try:
        result=verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256})
    except (ValueError,OSError,KeyError,TypeError) as e:
        print(json.dumps({'artifact_verification':'fail','reason':str(e),'mathematical_gate':False}));return 1
    print(json.dumps(result));return 0
if __name__=='__main__':sys.exit(main())
