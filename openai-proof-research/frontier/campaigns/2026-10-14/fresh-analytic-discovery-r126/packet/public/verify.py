#!/usr/bin/env python3
"""Read-only packet authentication. Requires externally supplied detached anchors.
Original code: MIT. No claim about mathematical correctness or contribution.
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

def audit(event, args):
    if event == 'open':
        mode = args[1] or ''
        flags = args[2] if len(args) > 2 else 0
        if any(c in str(mode) for c in 'wax+') or (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
            raise RuntimeError('read-only audit denied writable open')
    if event in {'os.remove', 'os.rename', 'os.mkdir', 'os.rmdir', 'os.chmod', 'os.chown', 'os.utime', 'os.link', 'os.symlink', 'os.truncate', 'subprocess.Popen', 'os.system', 'socket.connect', 'socket.bind'}:
        raise RuntimeError('read-only audit denied ' + event)

sys.addaudithook(audit)

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def pairs(items):
    result = {}
    for k, v in items:
        require(k not in result, 'duplicate JSON key: ' + k)
        result[k] = v
    return result

def readjson(path):
    return json.loads(path.read_bytes(), object_pairs_hook=pairs)

def safe(name):
    p = PurePosixPath(name)
    require(str(p) == name and not p.is_absolute() and '..' not in p.parts and name != '.', 'unsafe path')
    return name

def inventory(root):
    files, dirs = {}, ['.']
    require(root.is_dir() and not root.is_symlink(), 'packet root type')
    for base, children, names in os.walk(root, followlinks=False):
        for name in children + names:
            p = Path(base) / name
            mode = p.lstat().st_mode
            rel = p.relative_to(root).as_posix()
            safe(rel)
            if stat.S_ISDIR(mode):
                dirs.append(rel)
            elif stat.S_ISREG(mode):
                data = p.read_bytes()
                files[rel] = {'sha256': digest(data), 'bytes': len(data)}
            else:
                raise ValueError('nonregular packet entry: ' + rel)
    return files, sorted(dirs)

def run():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--expected-final', required=True)
    ap.add_argument('--expected-report', required=True)
    a = ap.parse_args()
    require(re.fullmatch('[0-9a-f]{64}', a.expected_final) is not None, 'bad detached final')
    require(re.fullmatch('[0-9a-f]{64}', a.expected_report) is not None, 'bad detached report')
    root = a.root
    require(root.is_dir() and not root.is_symlink(), 'author root type')
    for n in ['FINAL', 'REPORT.md', 'freeze-anchor.json']:
        require(stat.S_ISREG((root/n).lstat().st_mode), 'nonregular outer anchor')
    require((root/'FINAL').read_text() == a.expected_final+'\n', 'detached FINAL mismatch')
    require(digest((root/'REPORT.md').read_bytes()) == a.expected_report, 'outside report hash mismatch')
    packet = root/'packet'
    files, dirs = inventory(packet)
    require('MANIFEST.json' in files, 'missing manifest')
    require(files.pop('MANIFEST.json')['sha256'] == a.expected_final, 'manifest detached hash mismatch')
    m = readjson(packet/'MANIFEST.json')
    require(m.get('schema') == 'r126-exact-packet-v1' and m.get('pin') == PIN, 'manifest schema/pin')
    require(files == m['files'], 'exact payload set/hash/size mismatch')
    require(dirs == m['directories'], 'exact directory set mismatch')
    freeze = readjson(packet/'public/freeze-anchor.json')
    require((root/'freeze-anchor.json').read_bytes() == (packet/'public/freeze-anchor.json').read_bytes(), 'outside freeze anchor mismatch')
    for n, h in freeze['files'].items():
        require(digest((packet/'public'/safe(n)).read_bytes()) == h, 'frozen bytes changed: '+n)
    tree = readjson(packet/'private/context/preprints-tree.json')
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'incomplete canonical tree')
    canonical = {x['path']: x for x in tree['tree']}
    require(len(canonical) == 13223, 'duplicate canonical paths')
    reg = readjson(packet/'private/upstream/register.json')
    require(reg == readjson(packet/'public/source-map.json'), 'public canonical map differs')
    retained = 0
    for x in reg:
        c = x['canonical']
        require(canonical.get(c['path']) == c, 'canonical FULL record mismatch')
        require(x['url'] == 'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+c['path'], 'raw pinned URL mismatch')
        p = packet/safe(x['file'])
        if x['retained']:
            retained += 1
            data = p.read_bytes()
            require(len(data) == c['size'] and digest(data) == x['sha256'], 'canonical byte identity')
            blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            require(blob == c['sha'], 'Git blob mismatch')
        else:
            require(not p.exists(), 'removed acquisition unexpectedly present')
    successes, failures = 0, 0
    for x in readjson(packet/'private/primary/register.json'):
        if 'failure' in x:
            failures += 1
            continue
        successes += 1
        require(x['extraction_exit'] == 0, 'primary extraction failed')
        for ext, key in [('pdf', 'sha256'), ('txt', 'text_sha256')]:
            require(digest((packet/'private/primary'/(safe(x['name'])+'.'+ext)).read_bytes()) == x[key], 'primary identity mismatch')
    histories = readjson(packet/'private/history/register.json')
    for x in histories:
        data = (packet/safe(x['file'])).read_bytes()
        require(len(data) == x['bytes'] and digest(data) == x['sha256'], 'history copy mismatch')
    print(json.dumps({'integrity':'PASS', 'mathematical_gate':False, 'payloads':len(files), 'directories':len(dirs), 'canonical_records':len(reg), 'retained_canonical':retained, 'primary_pairs':successes, 'primary_failures':failures, 'history_copies':len(histories), 'detached_final':a.expected_final, 'outside_report':a.expected_report}, sort_keys=True))

if __name__ == '__main__':
    try:
        run()
    except Exception as e:
        print(json.dumps({'integrity':'REJECT','reason':str(e),'mathematical_gate':False}), file=sys.stderr)
        sys.exit(1)
