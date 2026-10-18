#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Verify archive or clean extraction against externally supplied manifest/gate hashes."""
import argparse
from pathlib import Path
import stat
import sys
sys.dont_write_bytecode = True
import zipfile
from bundle_common import public_path, verify_inputs, bound_anchors, check, directory_set, gate_check, parse, read, require, safe, sha


def verify(get,names,manifest_hash,gate_hash,actual_dirs=None):
    raw=get('BUNDLE-MANIFEST.json')
    require(sha(raw)==manifest_hash,'external manifest hash mismatch')
    manifest=parse(raw)
    require(manifest['gate_sha256']==gate_hash,'manifest gate mismatch')
    listed=set()
    for row in manifest['files']:
        name=row['path'];public_path(name);require(name not in listed,'duplicate manifest path')
        listed.add(name);check(get(name),row)
    require(set(names)==listed|{'BUNDLE-MANIFEST.json'},'exact membership mismatch')
    require(set(manifest['directories'])==directory_set(listed),'manifest directory mismatch')
    require(len(manifest['directories'])==len(set(manifest['directories'])),'duplicate directory')
    if actual_dirs is not None:require(actual_dirs==set(manifest['directories']),'exact directory membership mismatch')
    gate_raw=get('FINAL-GATE.json');require(sha(gate_raw)==gate_hash,'external gate hash mismatch')
    gate=parse(gate_raw);gate_check(gate)
    bound_anchors(get,gate)
    for row in gate['artifacts']:check(get(row['path']),row)
    selection=parse(get('payload-selection.json'))
    verify_inputs(get,selection,gate)
    return len(names)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('path',type=Path)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--gate-sha256',required=True)
    a=p.parse_args()
    require(not a.path.is_symlink(),'symlink root')
    if a.path.is_dir():
        names=[];dirs=set()
        for f in a.path.rglob('*'):
            require(not f.is_symlink(),'symlink entry')
            if stat.S_ISREG(f.lstat().st_mode):
                require(f.lstat().st_nlink == 1, 'hardlinked entry')
                names.append(f.relative_to(a.path).as_posix())
            else:
                require(f.is_dir(),'unsupported entry');dirs.add(f.relative_to(a.path).as_posix())
        count=verify(lambda name:read(a.path,name),names,a.manifest_sha256,a.gate_sha256,dirs)
    else:
        with zipfile.ZipFile(a.path) as archive:
            names=archive.namelist();require(len(names)==len(set(names)),'duplicate ZIP member')
            for member in archive.infolist():
                safe(member.filename)
                require(not member.is_dir() and stat.S_ISREG(member.external_attr>>16),'non-file ZIP member')
            count=verify(archive.read,names,a.manifest_sha256,a.gate_sha256)
    print('BUNDLE VERIFIED:',count,'files; no mathematical or priority inference')


if __name__=='__main__':
    try:main()
    except (OSError,ValueError,KeyError,TypeError,StopIteration,zipfile.BadZipFile) as exc:
        sys.exit('BUNDLE VERIFY FAILED: '+str(exc))
