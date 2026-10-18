#!/usr/bin/env python3
# Copyright2026 Myeongjin Kang. MIT.
"""Externally anchored exact preparation identity; no review verdict."""
import argparse,json,os,stat,sys
from pathlib import Path
sys.dont_write_bytecode=True
from bundle_common import parse,read,require,sha

def check(root,anchor):
    require(len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor),'bad anchor')
    raw=read(root,'manifest.json');require(sha(raw)==anchor,'external anchor mismatch')
    manifest=parse(raw);files={};dirs=['.']
    for base,ds,fs in os.walk(root,followlinks=False):
        for name in ds+fs:
            p=Path(base)/name;rel=str(p.relative_to(root));mode=p.lstat()
            require(not stat.S_ISLNK(mode.st_mode),'symlink entry')
            if stat.S_ISDIR(mode.st_mode):dirs.append(rel)
            else:
                require(stat.S_ISREG(mode.st_mode) and mode.st_nlink==1,'nonregular or hardlink')
                if rel!='manifest.json':
                    data=read(root,rel);files[rel]={'path':rel,'bytes':len(data),'sha256':sha(data)}
    require(sorted(dirs)==manifest['directories'],'directory inventory')
    require(sorted(files.values(),key=lambda x:x['path'])==manifest['files'],'file inventory')
    return {'status':'PASS_PREPARATION_SEAL_IDENTITY_ONLY','payloads':len(files),'directories':len(dirs)}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--expected-manifest-sha256',required=True);p.add_argument('--root',type=Path);a=p.parse_args()
    try:print(json.dumps(check(a.root.absolute() if a.root else Path(__file__).absolute().parent,a.expected_manifest_sha256)))
    except (OSError,ValueError,KeyError,TypeError) as e:sys.exit('REFUSED: '+str(e))
