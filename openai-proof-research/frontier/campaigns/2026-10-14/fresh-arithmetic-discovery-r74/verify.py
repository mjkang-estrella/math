#!/usr/bin/env python3
"""Read-only, offline exact-inventory verifier; requires a DETACHED anchor.
Integrity only. This code assigns no mathematical or contribution gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def safe_name(name):
    require(isinstance(name,str) and name and '\\' not in name, 'invalid path')
    q=PurePosixPath(name)
    require(not q.is_absolute() and str(q)==name and all(x not in ('..','.') for x in q.parts), 'unsafe path')
    return name

def unique_json(data):
    def pairs(items):
        out={}
        for k,v in items:
            require(k not in out, 'duplicate JSON key')
            out[k]=v
        return out
    return json.loads(data, object_pairs_hook=pairs)

def regular(path):
    s=path.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_nlink==1, 'nonregular, symbolic or hardlinked file: '+str(path))
    return path.read_bytes()

def verify(root, anchor):
    require(re.fullmatch('[0-9a-f]{64}',anchor) is not None, 'detached finalhash must be lowercase SHA256')
    root=Path(os.path.abspath(root))
    for q in [root,*root.parents]:
        require(not q.is_symlink(), 'symbolic directory ancestor')
    require(root.is_dir(), 'root is not a directory')
    raw=regular(root/'MANIFEST.json')
    require(digest(raw)==anchor, 'detached finalhash mismatch')
    m=unique_json(raw)
    require(set(m)=={'format','pin','scope_sha256','files','directories'}, 'manifest schema')
    require(m['format']=='T047S74-exact-v1' and m['pin']==PIN, 'manifest identity')
    require(isinstance(m['files'],list) and isinstance(m['directories'],list), 'manifest inventory types')
    expected={}
    for row in m['files']:
        require(set(row)=={'path','bytes','sha256'}, 'file record schema')
        n=safe_name(row['path'])
        require(n!='MANIFEST.json' and n not in expected,'duplicate or self-listed payload')
        require(type(row['bytes']) is int and row['bytes']>=0,'invalid byte count')
        require(isinstance(row['sha256'],str) and re.fullmatch('[0-9a-f]{64}',row['sha256']), 'invalid hash')
        expected[n]=row
    dirs=[safe_name(x) for x in m['directories']]
    require(len(set(dirs))==len(dirs),'duplicate directories')
    found_files=set(); found_dirs=set()
    for here, subdirs, filenames in os.walk(root,followlinks=False):
        base=Path(here)
        for n in subdirs:
            q=base/n
            require(stat.S_ISDIR(q.lstat().st_mode),'nonregular directory')
            found_dirs.add(q.relative_to(root).as_posix())
        for n in filenames:
            q=base/n; data=regular(q); rel=q.relative_to(root).as_posix()
            found_files.add(rel)
            if rel!='MANIFEST.json':
                require(rel in expected,'unexpected file: '+rel)
                require(len(data)==expected[rel]['bytes'] and digest(data)==expected[rel]['sha256'],'payload mismatch: '+rel)
    require(found_files==set(expected)|{'MANIFEST.json'},'missing files')
    require(found_dirs==set(dirs),'directory inventory mismatch')
    receipt=unique_json(regular(root/'freeze-receipt.json'))
    require(receipt['file']=='scope-freeze.md','scope filename')
    require(digest(regular(root/'scope-freeze.md'))==receipt['sha256']==m['scope_sha256'],'frozen scope mismatch')
    require(digest(regular(root/'prefreeze.md'))==receipt['prefreeze_sha256'],'prefreeze mismatch')
    for r in unique_json(regular(root/'source-receipts.json')):
        safe_name(r['local']); safe_name(r['path'])
        require(r['local']=='private/upstream/'+r['path'],'source local path mismatch')
        data=regular(root/r['local'])
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(blob==r['git_blob'] and digest(data)==r['sha256'] and len(data)==r['bytes'],'source receipt mismatch')
        require(r['raw_url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path'],'source pin mismatch')
    for r in unique_json(regular(root/'primary-receipts.json')):
        if r['status']=='failed':
            continue
        require(r['status']=='success','unknown primary status')
        safe_name(r['file']); data=regular(root/r['file'])
        require(digest(data)==r['sha256'] and len(data)==r['bytes'],'primary PDF mismatch')
        require(digest(regular((root/r['file']).with_suffix('.txt')))==r['text_sha256'],'primary extraction mismatch')
    status=unique_json(regular(root/'status.json'))
    require(status['research_status']=='FULL_SCOPE_UNRESOLVED' and status['nominee'] is False,'archive status mismatch')
    return {'integrity':'verified','payload_files':len(expected),'directories':len(dirs),'research_status':'FULL_SCOPE_UNRESOLVED','mathematical_gate':False}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--finalhash',required=True,help='DETACHED SHA256 of MANIFEST.json; never read an in-packet anchor')
    ap.add_argument('--root',default=str(Path(__file__).absolute().parent))
    args=ap.parse_args()
    try:
        print(json.dumps(verify(args.root,args.finalhash),sort_keys=True))
    except (ValueError,OSError,KeyError,TypeError) as error:
        print('INTEGRITY FAILURE: '+str(error),file=sys.stderr)
        return 1
    return 0

if __name__=='__main__':
    sys.exit(main())
