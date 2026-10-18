#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Verify canonical local release exact inventory against an external seal."""
import argparse,stat,sys
from pathlib import Path
sys.dont_write_bytecode=True
from bundle_common import parse,sha,read,check,require,directory_set
p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('--manifest-sha256',required=True);a=p.parse_args()
try:
    raw=read(a.root,'manifest.json');require(sha(raw)==a.manifest_sha256,'external seal mismatch');m=parse(raw)
    files=set();dirs=set()
    for f in a.root.rglob('*'):
        require(not f.is_symlink(),'symlink entry')
        if f.is_dir():dirs.add(f.relative_to(a.root).as_posix())
        else:
            require(stat.S_ISREG(f.lstat().st_mode) and f.lstat().st_nlink==1,'nonregular/hardlinked entry');files.add(f.relative_to(a.root).as_posix())
    listed=set()
    for row in m['files']:
        require(row['path'] not in listed,'duplicate path');listed.add(row['path']);check(read(a.root,row['path']),row)
    require(files==listed|{'manifest.json'},'file membership changed')
    require(dirs==set(m['directories'])==directory_set(listed),'directory membership changed')
    print('RELEASE SEAL VERIFIED:',len(listed),'payload files; no acceptance')
except (OSError,ValueError,KeyError,TypeError) as e:sys.exit('RELEASE SEAL FAILED: '+str(e))
