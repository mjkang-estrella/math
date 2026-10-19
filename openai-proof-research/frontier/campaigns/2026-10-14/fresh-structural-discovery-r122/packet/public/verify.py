#!/usr/bin/env python3
"""Read-only r122 archive verifier. Integrity only; no mathematical gates."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_HASH = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
STATUS = 'PREFREEZE_NO_TARGET_NO_NOMINEE'


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pairs(items):
    out = {}
    for k, v in items:
        require(k not in out, 'duplicate JSON key')
        out[k] = v
    return out


def decode(data):
    return json.loads(data, object_pairs_hook=pairs)


def safe_path(s):
    require(isinstance(s, str) and s and '\\' not in s, 'unsafe manifest path')
    q = PurePosixPath(s)
    require(not q.is_absolute() and '..' not in q.parts and '.' not in q.parts
            and q.as_posix() == s, 'unsafe manifest path')
    return s


def check_ancestors(path):
    path = path.absolute()
    for q in [*reversed(path.parents), path]:
        require(not stat.S_ISLNK(q.lstat().st_mode), 'symlink path or ancestor')


def read(path):
    check_ancestors(path)
    st = path.lstat()
    require(stat.S_ISREG(st.st_mode), 'nonregular file')
    require(st.st_nlink == 1, 'hardlinked file')
    return path.read_bytes()


def inventory(packet):
    check_ancestors(packet)
    require(packet.is_dir(), 'packet not directory')
    files, dirs = {}, []
    def walk(d):
        for p in sorted(d.iterdir()):
            s = p.relative_to(packet).as_posix()
            safe_path(s)
            st = p.lstat()
            require(not stat.S_ISLNK(st.st_mode), 'symlink payload')
            if stat.S_ISDIR(st.st_mode):
                dirs.append(s)
                walk(p)
            else:
                require(stat.S_ISREG(st.st_mode), 'nonregular payload')
                require(st.st_nlink == 1, 'hardlinked payload')
                b = p.read_bytes()
                files[s] = {'path': s, 'bytes': len(b), 'sha256': sha(b),
                            'mode': stat.S_IMODE(st.st_mode)}
    walk(packet)
    return [files[k] for k in sorted(files)], sorted(dirs)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--tree', required=True, type=Path)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    a = ap.parse_args()
    require(re.fullmatch('[0-9a-f]{64}', a.finalhash) is not None, 'invalid detached finalhash')
    require(re.fullmatch('[0-9a-f]{64}', a.reporthash) is not None, 'invalid detached reporthash')
    root = a.root.absolute()
    check_ancestors(root)
    fb = read(root / 'FINAL.json')
    require(sha(fb) == a.finalhash, 'detached FINAL hash mismatch')
    f = decode(fb)
    require(set(f) == {'schema', 'status', 'pin', 'manifest_sha256', 'report_sha256',
                       'packet_report_sha256', 'verifier_sha256', 'tree_sha256'}, 'FINAL schema')
    require(f['schema'] == 'r122-final-v1' and f['status'] == STATUS and f['pin'] == PIN,
            'FINAL status or pin')
    require(f['tree_sha256'] == TREE_HASH, 'FINAL canonical tree identity')
    rb = read(root / 'REPORT.md')
    require(sha(rb) == a.reporthash == f['report_sha256'], 'detached report hash mismatch')
    mb = read(root / 'MANIFEST.json')
    require(sha(mb) == f['manifest_sha256'], 'manifest hash mismatch')
    m = decode(mb)
    require(set(m) == {'schema', 'files', 'directories'} and m['schema'] == 'r122-manifest-v1',
            'manifest schema')
    for x in m['files']:
        require(set(x) == {'path', 'bytes', 'sha256', 'mode'}, 'manifest record schema')
        safe_path(x['path'])
    for x in m['directories']:
        safe_path(x)
    require(len({x['path'] for x in m['files']}) == len(m['files']), 'duplicate manifest path')
    require(len(set(m['directories'])) == len(m['directories']), 'duplicate manifest directory')
    actual_files, actual_dirs = inventory(root / 'packet')
    require([x['path'] for x in actual_files] == [x['path'] for x in m['files']],
            'packet file membership mismatch')
    require(actual_dirs == m['directories'], 'packet directory membership mismatch')
    require(actual_files == m['files'], 'payload bytes, mode or hash mismatch')
    p = root / 'packet'
    require(sha(read(p / 'public/report.md')) == f['packet_report_sha256'], 'packet report binding')
    require(sha(read(p / 'public/verify.py')) == f['verifier_sha256'], 'verifier payload binding')
    require(sha(read(Path(__file__))) == f['verifier_sha256'], 'running verifier binding')
    tb = read(a.tree)
    require(sha(tb) == TREE_HASH, 'canonical tree hash mismatch')
    tree = decode(tb)
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'canonical tree completeness')
    ix = {r['path']: r for r in tree['tree']}
    require(len(ix) == 13223, 'duplicate canonical tree path')
    receipt = decode(read(p / 'public/tree-receipt.json'))
    require(receipt == {'commit': PIN, 'entries': 13223, 'truncated': False, 'sha256': TREE_HASH},
            'tree receipt mismatch')
    sources = decode(read(p / 'public/source-register.json'))
    selection = decode(read(p / 'public/canonical-selection.json'))
    require(len(sources) == 12, 'source register cardinality')
    require(len({r['canonical_path'] for r in sources}) == len(sources), 'duplicate source canonical')
    require(selection == [ix[r['canonical_path']] for r in sources], 'canonical selection mismatch')
    for r in sources:
        c = safe_path(r['canonical_path'])
        require(c in ix and ix[c]['type'] == 'blob', 'source canonical identity')
        require(r['path'] == 'private/upstream/' + c, 'source storage path')
        require(r['raw_url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + c,
                'source raw URL mismatch')
        b = read(p / safe_path(r['path']))
        require(sha(b) == r['sha256'] and len(b) == r['bytes'], 'source bytes/hash mismatch')
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        require(blob == r['git_blob'] == ix[c]['sha'], 'source Git blob mismatch')
        require(re.findall(r'\\label\{([^}]+)\}', b.decode()) == r['labels'], 'source label metadata mismatch')
    actual_source = {x['path'] for x in actual_files if x['path'].startswith('private/upstream/')}
    require(actual_source == {r['path'] for r in sources}, 'unregistered source body')
    primaries = decode(read(p / 'public/primary-register.json'))
    require(len(primaries) == 8 and len({r['name'] for r in primaries}) == 8, 'primary count')
    expected_primary = set()
    for r in primaries:
        require(r['status'] == 'success', 'primary status')
        ident = re.search(r'(\d{4}\.\d{4,5}v\d+)$', r['name'])
        require(ident and r['requested_url'] == 'https://arxiv.org/pdf/' + ident.group(1), 'primary version URL')
        require(r['resolved_url'] == r['requested_url'], 'primary resolved URL')
        for key, suffix in [('pdf', 'pdf'), ('text', 'txt')]:
            path = 'private/primary/' + r['name'] + '.' + suffix
            require(r[key] == path, 'primary storage path')
            b = read(p / path)
            require(sha(b) == r[key + '_sha256'], 'primary bytes/hash mismatch')
            if key == 'pdf': require(b.startswith(b'%PDF'), 'primary PDF header')
            expected_primary.add(path)
    require({x['path'] for x in actual_files if x['path'].startswith('private/primary/')} == expected_primary,
            'unregistered primary body')
    histories = decode(read(p / 'public/history-register.json'))
    require(len(histories) == 13, 'history count')
    for r in histories:
        safe_path(r['origin'])
        b = read(p / safe_path(r['path']))
        require(len(b) == r['bytes'] and sha(b) == r['sha256'], 'history copy bytes/hash')
        require(1 <= r['first_line'] <= r['last_line'], 'history span')
    require({x['path'] for x in actual_files if x['path'].startswith('private/history/') and x['path'].endswith('.md')} == {r['path'] for r in histories}, 'unregistered history body')
    print(json.dumps({'status': 'INTEGRITY_VERIFIED_ONLY', 'files': len(actual_files),
                      'directories': len(actual_dirs), 'canonical_bodies': len(sources),
                      'primary_pairs': len(primaries),
                      'history_copies': len(histories), 'tree_entries': 13223,
                      'final_sha256': a.finalhash, 'report_sha256': a.reporthash}, sort_keys=True))


if __name__ == '__main__':
    def read_only(event, args):
        if event == 'open':
            mode = args[1] if len(args) > 1 else None
            flags = args[2] if len(args) > 2 else 0
            if (isinstance(mode, str) and any(x in mode for x in 'wax+')) or (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
                raise ValueError('read-only audit: write open')
        if event in {'os.remove', 'os.rename', 'os.mkdir', 'os.rmdir', 'os.chmod', 'os.link', 'os.symlink', 'subprocess.Popen', 'socket.connect'}:
            raise ValueError('read-only audit: mutation or external operation')
    sys.addaudithook(read_only)
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print('REJECT: ' + str(exc), file=sys.stderr)
        sys.exit(1)
