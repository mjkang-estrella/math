#!/usr/bin/env python3
"""Read-only artifact verifier. Supply all three detached SHA256 anchors explicitly.
Usage: python verify_packet.py ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256
This checks bytes, modes and membership; it does not check mathematics.
"""
from pathlib import Path, PurePosixPath
import hashlib, json, os, stat, sys

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda:stream.read(1048576),b''): h.update(chunk)
    return h.hexdigest()

def require(condition,message):
    if not condition: raise ValueError(message)

def main():
    require(len(sys.argv)==5,'supply ROOT and all three detached anchors')
    root=Path(sys.argv[1]).resolve()
    names=('FINAL.md','MANIFEST.json','REPORT.md')
    for name,anchor in zip(names,sys.argv[2:]):
        require(len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor),'invalid explicit anchor')
        p=root/name
        require(p.is_file() and not p.is_symlink(),'missing or symbolic envelope '+name)
        require(sha(p)==anchor,'detached anchor mismatch: '+name)
    manifest=json.loads((root/'MANIFEST.json').read_text())
    require(manifest['schema']=='r136-exact-packet-v1','unexpected schema')
    expected=set(names)
    for record in manifest['files']:
        rel=record['path']; q=PurePosixPath(rel)
        require(not q.is_absolute() and '..' not in q.parts and str(q)==rel,'unsafe member')
        require(rel not in expected,'duplicate or envelope member')
        expected.add(rel); p=root.joinpath(*q.parts)
        require(p.is_file() and not p.is_symlink(),'missing or symbolic member '+rel)
        require(p.stat().st_size==record['bytes'],'size mismatch '+rel)
        require(oct(stat.S_IMODE(p.stat().st_mode))==record['mode'],'mode mismatch '+rel)
        require(sha(p)==record['sha256'],'hash mismatch '+rel)
    actual=set()
    for base,dirs,files in os.walk(root,followlinks=False):
        for name in dirs:
            require(not (Path(base)/name).is_symlink(),'symbolic directory')
        for name in files:
            p=Path(base)/name
            require(not p.is_symlink(),'symbolic file')
            actual.add(p.relative_to(root).as_posix())
    require(actual==expected,'packet membership mismatch')
    frozen=json.loads((root/'private/freeze.json').read_text())
    require(sha(root/'FROZEN.md')==frozen['sha256'],'frozen statement changed')
    print(json.dumps({'artifact_integrity':'matches explicit detached anchors','payload_files':len(manifest['files']),'mathematical_verdict':None}))

if __name__=='__main__':
    try: main()
    except (ValueError,OSError,KeyError,json.JSONDecodeError) as error:
        print(str(error),file=sys.stderr);sys.exit(1)
