"""Read-only exact packet artifact verifier. No mathematical assessment.
Supply all three detached anchors independently. The selected membership is
packet/, with explicit MANIFEST.json and outside REPORT.txt anchors. Other
outside files, including DETACHED.json and copied-control workspace, are not
members. No imports of packet code, writes, network or subprocesses.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

FORMAT = 'structural-r197-contribution-exact-packet-v1'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def mode(path):
    return format(stat.S_IMODE(path.lstat().st_mode), '04o')

def read_regular(path):
    require(stat.S_ISREG(path.lstat().st_mode), 'not a regular non-symlink file: '+str(path))
    return path.read_bytes()

def inventory(packet):
    require(stat.S_ISDIR(packet.lstat().st_mode), 'packet is not a non-symlink directory')
    files = {}
    dirs = {'.': mode(packet)}
    for base, children, names in os.walk(packet, topdown=True, followlinks=False):
        for name in children:
            path = Path(base)/name
            require(stat.S_ISDIR(path.lstat().st_mode), 'non-directory or symlink child: '+str(path))
            dirs[path.relative_to(packet).as_posix()] = mode(path)
        for name in names:
            path = Path(base)/name
            data = read_regular(path)
            rel = path.relative_to(packet).as_posix()
            files[rel] = {'path':rel, 'bytes':len(data), 'sha256':digest(data), 'mode':mode(path)}
    return files, dirs

def safe_path(name):
    path = PurePosixPath(name)
    return bool(name) and not path.is_absolute() and '..' not in path.parts and path.as_posix()==name

def verify(root, final_sha256, manifest_sha256, report_sha256):
    for anchor in [final_sha256, manifest_sha256, report_sha256]:
        require(re.fullmatch('[0-9a-f]{64}',anchor) is not None, 'malformed detached anchor')
    require(stat.S_ISDIR(root.lstat().st_mode), 'root is not a non-symlink directory')
    mb = read_regular(root/'MANIFEST.json')
    rb = read_regular(root/'REPORT.txt')
    require(digest(mb)==manifest_sha256, 'detached MANIFEST mismatch')
    require(digest(rb)==report_sha256, 'detached REPORT mismatch')
    require(mode(root/'MANIFEST.json')=='0444' and mode(root/'REPORT.txt')=='0444', 'outside anchor carrier mode mismatch')
    manifest = json.loads(mb)
    require(manifest['format']==FORMAT and manifest['selection']=='packet/', 'unexpected selection format')
    expected = {}
    for entry in manifest['files']:
        name = entry['path']
        require(safe_path(name) and name not in expected, 'unsafe or duplicate file path')
        expected[name] = entry
    directories = {}
    for entry in manifest['directories']:
        name = entry['path']
        require(safe_path(name) and name not in directories, 'unsafe or duplicate directory path')
        directories[name] = entry['mode']
    files, dirs = inventory(root/'packet')
    require(set(files)==set(expected), 'exact file membership mismatch')
    require(dirs==directories, 'exact directory membership/modes mismatch')
    for name in sorted(expected):
        require(files[name]==expected[name], 'file bytes/hash/mode mismatch: '+name)
    require(files['FINAL.txt']['sha256']==final_sha256, 'detached FINAL mismatch')
    require(files['FINAL.txt']['mode']=='0444', 'FINAL mode mismatch')
    return {'artifact_verification':'succeeded','read_only':True,'files':len(files),'directories':len(dirs),'mathematics':'not assessed','correctness_condition':'not discharged by artifact verification'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args.root,args.final_sha256,args.manifest_sha256,args.report_sha256),sort_keys=True))
        return 0
    except Exception as error:
        print(json.dumps({'artifact_verification':'failed','reason':str(error)},sort_keys=True))
        return 1

if __name__ == '__main__':
    sys.exit(main())
