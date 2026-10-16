#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Verify archive or clean extraction against externally supplied manifest/gate hashes."""
import argparse
from pathlib import Path
import stat
import sys
import zipfile
from bundle_common import check, gate_check, parse, read, require, safe, sha


def verify(get,names,manifest_hash,gate_hash):
    raw=get('BUNDLE-MANIFEST.json')
    require(sha(raw)==manifest_hash,'external manifest hash mismatch')
    manifest=parse(raw)
    require(manifest['gate_sha256']==gate_hash,'manifest gate mismatch')
    listed=set()
    for row in manifest['files']:
        name=row['path'];safe(name);require(name not in listed,'duplicate manifest path')
        listed.add(name);check(get(name),row)
    require(set(names)==listed|{'BUNDLE-MANIFEST.json'},'exact membership mismatch')
    gate_raw=get('FINAL-GATE.json');require(sha(gate_raw)==gate_hash,'external gate hash mismatch')
    gate=parse(gate_raw);gate_check(gate)
    for row in gate['artifacts']:check(get(row['path']),row)
    return len(names)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('path',type=Path)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--gate-sha256',required=True)
    a=p.parse_args()
    if a.path.is_dir():
        names=[]
        for f in a.path.rglob('*'):
            require(not f.is_symlink(),'symlink entry')
            if f.is_file():names.append(f.relative_to(a.path).as_posix())
            else:require(f.is_dir(),'unsupported entry')
        count=verify(lambda name:read(a.path,name),names,a.manifest_sha256,a.gate_sha256)
    else:
        with zipfile.ZipFile(a.path) as archive:
            names=archive.namelist();require(len(names)==len(set(names)),'duplicate ZIP member')
            for member in archive.infolist():
                safe(member.filename)
                require(not member.is_dir() and not stat.S_ISLNK(member.external_attr>>16),'non-file ZIP member')
            count=verify(archive.read,names,a.manifest_sha256,a.gate_sha256)
    print('BUNDLE VERIFIED:',count,'files; no mathematical or priority inference')


if __name__=='__main__':
    try:main()
    except (OSError,ValueError,KeyError,TypeError,zipfile.BadZipFile) as exc:
        sys.exit('BUNDLE VERIFY FAILED: '+str(exc))
