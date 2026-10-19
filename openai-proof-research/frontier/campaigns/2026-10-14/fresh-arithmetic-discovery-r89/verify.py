#!/usr/bin/env python3
"""Original MIT integrity verifier. No mathematical or contribution gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
RAW = 'https://raw.githubusercontent.com/openai/math/' + PIN + '/'

def lock_down():
    def audit(event, args):
        if event == 'open':
            mode, flags = args[1:3]
            if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
                raise PermissionError('READ_ONLY: open')
        if event.startswith(('socket.', 'subprocess.')) or event in {'os.system','os.posix_spawn','os.posix_spawnp','os.fork','os.exec','os.remove','os.unlink','os.rename','os.rmdir','os.mkdir','os.symlink','os.link','os.chmod','os.chown','os.truncate','os.utime'}:
            raise PermissionError('READ_ONLY: ' + event)
    sys.addaudithook(audit)

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def pairs(items):
    out = {}
    for key, value in items:
        require(key not in out, 'duplicate JSON key')
        out[key] = value
    return out

def read_json(path):
    return json.loads(path.read_bytes(), object_pairs_hook=pairs)

def relative(s):
    require(isinstance(s, str) and s and '\\' not in s and not s.startswith('/'), 'unsafe relative path')
    require(all(x not in {'', '.', '..'} for x in s.split('/')), 'unsafe path component')
    require(PurePosixPath(s).as_posix() == s, 'noncanonical path')
    return s

def file_bytes(path):
    require(stat.S_ISREG(path.lstat().st_mode), 'not a regular file: ' + str(path))
    return path.read_bytes()

def inventory(root):
    require(stat.S_ISDIR(root.lstat().st_mode), 'not a directory')
    files, dirs = {}, ['']
    def walk(folder):
        for item in sorted(os.scandir(folder), key=lambda x: x.name):
            path = Path(item.path)
            rel = path.relative_to(root).as_posix()
            relative(rel)
            mode = item.stat(follow_symlinks=False).st_mode
            if stat.S_ISDIR(mode):
                dirs.append(rel); walk(path)
            else:
                require(stat.S_ISREG(mode), 'special file or symlink: ' + rel)
                b = file_bytes(path)
                files[rel] = {'bytes': len(b), 'sha256': digest(b)}
    walk(root)
    return files, sorted(dirs)

def verify(root, finalhash, reporthash, treepath):
    for h in (finalhash, reporthash):
        require(re.fullmatch('[0-9a-f]{64}', h) is not None, 'invalid detached anchor')
    require(not root.is_symlink(), 'symlink root')
    finalbytes = file_bytes(root/'FINAL.json')
    require(digest(finalbytes) == finalhash, 'FINAL anchor mismatch')
    final = read_json(root/'FINAL.json')
    require(final['schema'] == 'r89-final-v1' and final['status'] == 'PREFREEZE_NO_NOMINEE', 'wrong final identity')
    require(final['pin'] == PIN and final['frozen_target'] is False, 'scope identity')
    rb = file_bytes(root/'REPORT.md')
    require(digest(rb) == reporthash == final['report_sha256'], 'REPORT anchor mismatch')
    for name in ('verify.py','run_controls.py'):
        require(digest(file_bytes(root/name)) == final['code'][name], 'code identity: ' + name)
    require(Path(__file__).resolve() == (root/'verify.py').resolve(), 'run the owned/copied verifier')
    packet = root/'packet'
    mb = file_bytes(packet/'MANIFEST.json')
    require(digest(mb) == final['manifest_sha256'], 'manifest anchor mismatch')
    manifest = read_json(packet/'MANIFEST.json')
    require(manifest['schema'] == 'r89-packet-v1', 'manifest schema')
    expected = {}
    for item in manifest['files']:
        p = relative(item['path'])
        require(p != 'MANIFEST.json' and p not in expected, 'duplicate/self payload')
        expected[p] = {'bytes':item['bytes'], 'sha256':item['sha256']}
    dirs = manifest['directories']
    require(dirs == sorted(set(dirs)) and '' in dirs, 'directory inventory shape')
    for d in dirs:
        if d: relative(d)
    actual, actualdirs = inventory(packet)
    actual.pop('MANIFEST.json')
    require(actual == expected, 'exact payload inventory/hash mismatch')
    require(actualdirs == dirs, 'exact directory inventory mismatch')
    context = read_json(packet/'private/context.json')
    tb = file_bytes(treepath)
    expected_tree = next(x for x in context['records'] if x['path']=='sources/preprints-tree.json')
    require(digest(tb)==expected_tree['sha256'] and len(tb)==expected_tree['bytes'], 'external tree identity')
    tree = json.loads(tb, object_pairs_hook=pairs)
    require(tree['truncated'] is False and len(tree['tree'])==13223, 'complete tree required')
    canonical = {x['path']: x for x in tree['tree']}
    require(len(canonical)==13223, 'duplicate tree path')
    acq = read_json(packet/'private/acquisition.json')
    seen = set(); retained = 0
    for a in acq:
        c = a['canonical']; p = c['path']
        require(p not in seen, 'duplicate acquisition'); seen.add(p)
        require(c == canonical.get(p), 'FULL canonical record mismatch')
        require(a['pinned_url'] == RAW+p, 'pinned URL mismatch')
        require(c['type']=='blob' and c['mode']=='100644', 'canonical source type')
        local = relative(a['local'])
        require(local == 'packet/private/upstream/'+p, 'source location mismatch')
        require(re.fullmatch('[0-9a-f]{64}', a['sha256']) is not None, 'source SHA256 format')
        f = root/local
        if a['retained']:
            retained += 1; b = file_bytes(f)
            require(len(b)==c['size'] and digest(b)==a['sha256'], 'source bytes')
            require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==c['sha'], 'source Git blob')
        else:
            require(not f.exists() and not f.is_symlink(), 'removed source unexpectedly retained')
    for a in read_json(packet/'private/primary/register.json'):
        b = file_bytes(packet/'private/primary'/relative(a['pdf']))
        require(b.startswith(b'%PDF-') and len(b)==a['bytes'] and digest(b)==a['sha256'], 'primary PDF identity')
        t = file_bytes(packet/'private/primary'/relative(a['text']))
        require(t and digest(t)==a['text_sha256'] and a['extraction']==0, 'primary extraction identity')
    for a in read_json(packet/'private/history/register.json'):
        b = file_bytes(root/relative(a['local']))
        require(len(b)==a['bytes'] and digest(b)==a['sha256'], 'history copy identity')
    require(final['public_report_sha256']==digest(file_bytes(packet/'public/report.md')), 'public report identity')
    return {'integrity':'VERIFIED','payloads':len(expected),'directories_including_root':len(dirs),'canonical_records':len(acq),'retained_sources':retained,'removed_sources':len(acq)-retained,'mathematical_gate':False}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--finalhash', required=True)
    parser.add_argument('--reporthash', required=True)
    parser.add_argument('--tree', required=True, type=Path)
    args = parser.parse_args()
    lock_down()
    try:
        result = verify(args.root, args.finalhash, args.reporthash, args.tree)
    except Exception as e:
        print(json.dumps({'integrity':'REJECTED','reason':str(e)})); return 1
    print(json.dumps(result,sort_keys=True)); return 0

if __name__ == '__main__':
    sys.exit(main())
