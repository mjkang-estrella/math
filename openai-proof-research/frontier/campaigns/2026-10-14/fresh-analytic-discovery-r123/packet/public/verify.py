#!/usr/bin/env python3
"""Read-only r123 integrity verifier; not a mathematical gate."""
# Adapted from analytic r122 original integrity code; see RIGHTS.md.
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_HASH = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def guard(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if ((isinstance(mode, str) and any(c in mode for c in 'wax+')) or
            (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND))):
            raise PermissionError('verifier denies write open')
    if event in {'os.remove', 'os.rename', 'os.rmdir', 'os.mkdir', 'os.link', 'os.symlink', 'os.chmod', 'os.chown', 'os.truncate', 'os.utime', 'os.system', 'subprocess.Popen'} or event.startswith('socket.'):
        raise PermissionError('verifier denies mutation/network/process: ' + event)
sys.addaudithook(guard)

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def read(p):
    s = p.lstat()
    require(stat.S_ISREG(s.st_mode), 'not regular: ' + str(p))
    require(s.st_nlink == 1, 'hard link: ' + str(p))
    return p.read_bytes()

def rel(s):
    p = Path(s)
    require(isinstance(s, str) and bool(s) and not p.is_absolute() and p.as_posix() == s and all(x not in ('', '.', '..') for x in p.parts), 'unsafe relative path')
    return p

def inventory(packet):
    require(packet.is_dir() and not packet.is_symlink(), 'unsafe packet')
    files, directories = {}, {'': stat.S_IMODE(packet.lstat().st_mode)}
    for p in sorted(packet.rglob('*')):
        s, st = p.relative_to(packet).as_posix(), p.lstat()
        if stat.S_ISDIR(st.st_mode):
            directories[s] = stat.S_IMODE(st.st_mode)
        else:
            b = read(p)
            files[s] = {'sha256': sha(b), 'bytes': len(b), 'mode': stat.S_IMODE(st.st_mode)}
    return files, directories

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root', type=Path)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    ap.add_argument('--tree', type=Path, required=True)
    a = ap.parse_args()
    root = a.root.absolute()
    require(root.is_dir() and not root.is_symlink(), 'unsafe root')
    for value in (a.finalhash, a.reporthash):
        require(len(value) == 64 and all(c in '0123456789abcdef' for c in value), 'invalid detached hash')
    fb = read(root / 'FINAL.json')
    require(sha(fb) == a.finalhash, 'detached FINAL mismatch')
    f = json.loads(fb)
    require(f['pin'] == PIN and f['status'] == 'PREFREEZE_NO_NOMINEE' and f['frozen'] is False and f['nominee'] is None, 'status/pin mismatch')
    require(f['count_assignment'] is None and f['gate_assignment'] is None, 'forbidden assignment')
    mb = read(root / 'MANIFEST.json')
    require(sha(mb) == f['manifest_sha256'], 'manifest anchor mismatch')
    m = json.loads(mb)
    require(m['pin'] == PIN and m['format'] == 'r123-exact-packet-v1', 'manifest format')
    files, directories = inventory(root / 'packet')
    for p in m['files']:
        rel(p)
    for p in m['directories']:
        if p:
            rel(p)
    require(files == m['files'], 'exact file membership/hash/size/mode mismatch')
    require(directories == m['directories'], 'exact directory membership/mode mismatch')
    packet = root / 'packet'
    require(sha(read(packet / 'public/report.md')) == a.reporthash == f['report_sha256'], 'detached report mismatch')
    tb = read(a.tree)
    require(sha(tb) == TREE_HASH, 'canonical tree hash mismatch')
    require(read(packet / 'private/context/preprints-tree.json') == tb, 'private canonical tree mismatch')
    tree = json.loads(tb)
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'complete tree contract')
    mapping = {x['path']: x for x in tree['tree']}
    require(len(mapping) == 13223, 'duplicate canonical tree path')
    sources = json.loads(read(packet / 'public/source-register.json'))
    seen = set()
    for x in sources:
        require(x['path'] not in seen, 'duplicate source path')
        seen.add(x['path'])
        require(x['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + x['path'], 'pinned raw URL mismatch')
        b = read(packet / rel(x['local']))
        e = mapping[x['path']]
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        require(e['type'] == 'blob' and e['sha'] == x['blob'] == blob and e['size'] == x['size'] == len(b), 'canonical Git blob/size mismatch')
        require(sha(b) == x['sha256'] and len(b) == x['size'], 'source receipt mismatch')
    removed = json.loads(read(packet / 'public/acquisition-removed.json'))
    for x in removed:
        require(not (packet / rel(x['local'])).exists(), 'removed acquisition present')
        require(mapping[x['path']]['type'] == 'blob' and mapping[x['path']]['sha'] == x['blob'] and mapping[x['path']]['size'] == x['size'] and x['retained'] is False, 'removed canonical metadata mismatch')
        require(x['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + x['path'], 'removed pinned URL mismatch')
    primaries = json.loads(read(packet / 'public/primary-register.json'))
    for x in primaries:
        require(x['url'].startswith('https://'), 'primary URL mismatch')
        if x['success'] is False:
            require(bool(x['failure']) and 'pdf' not in x and 'text' not in x, 'failed acquisition claims body')
            continue
        require(x['success'] is True, 'primary status mismatch')
        for key in ('pdf', 'text'):
            require(sha(read(packet / rel(x[key]))) == x[key + '_sha256'], 'primary binding mismatch')
    for register in ('history-register.json', 'context-register.json', 'render-register.json', 'search-register.json'):
        for x in json.loads(read(packet / 'public' / register)):
            require(sha(read(packet / rel(x['local']))) == x['sha256'], 'history/context binding mismatch')
    print(json.dumps({'artifact_integrity': 'verified', 'mathematical_gate': False, 'files': len(files), 'directories': len(directories), 'canonical_sources': len(sources), 'removed_acquisitions': len(removed), 'primary_pairs': sum(x['success'] for x in primaries), 'primary_failures': sum(not x['success'] for x in primaries), 'final_sha256': a.finalhash, 'report_sha256': a.reporthash}, sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('VERIFY_FAILED: ' + str(e), file=sys.stderr)
        sys.exit(1)
