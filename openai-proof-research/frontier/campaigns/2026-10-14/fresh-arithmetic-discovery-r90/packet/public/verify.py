#!/usr/bin/env python3
"""Read-only r90 evidence verifier. Requires externally supplied anchors. MIT."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def audit(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (
            isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)
        ):
            raise PermissionError('READ_ONLY: open')
    if event in {'os.remove', 'os.rmdir', 'os.mkdir', 'os.rename', 'os.link', 'os.symlink',
                 'os.chmod', 'os.chown', 'os.truncate', 'os.utime', 'os.system',
                 'os.exec', 'os.posix_spawn', 'os.fork', 'subprocess.Popen'} or event.startswith('socket.'):
        raise PermissionError('READ_ONLY: ' + event)


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def regular(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'REGULAR_SINGLE_LINK: ' + str(path))
    return path.read_bytes()


def relpath(value):
    require(isinstance(value, str) and value and '\\' not in value, 'PATH')
    q = PurePosixPath(value)
    require(not q.is_absolute() and '..' not in q.parts and '.' not in q.parts and str(q) == value, 'PATH')
    return value


def walk(root):
    files, dirs = {}, {'.': stat.S_IMODE(root.lstat().st_mode)}
    require(stat.S_ISDIR(root.lstat().st_mode), 'PACKET_ROOT')
    for parent, subdirs, names in os.walk(root, followlinks=False):
        for name in sorted(subdirs + names):
            p = Path(parent) / name
            key = p.relative_to(root).as_posix()
            s = p.lstat()
            if stat.S_ISDIR(s.st_mode):
                dirs[key] = stat.S_IMODE(s.st_mode)
            else:
                require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'REGULAR_SINGLE_LINK: ' + key)
                b = p.read_bytes()
                files[key] = {'sha256': digest(b), 'bytes': len(b), 'mode': stat.S_IMODE(s.st_mode)}
    return files, dirs


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    ap.add_argument('--canonical-tree', required=True)
    a = ap.parse_args()
    sys.addaudithook(audit)
    for h in [a.finalhash, a.reporthash]:
        require(re.fullmatch('[0-9a-f]{64}', h), 'DETACHED_HASH_FORMAT')
    root = Path(a.root).absolute()
    packet = root / 'packet'
    fb = regular(root / 'FINAL.json')
    require(digest(fb) == a.finalhash, 'FINAL_HASH')
    final = json.loads(fb)
    rb = regular(root / 'REPORT.md')
    require(digest(rb) == a.reporthash == final['report_sha256'], 'REPORT_HASH')
    require(final['pin'] == PIN and final['tree_sha256'] == TREE, 'PIN_TREE_BINDING')
    require(final['status'] == 'PREFREEZE_NO_NOMINEE', 'STATUS')
    require(digest(regular(packet / 'public/verify.py')) == final['verifier_sha256'], 'VERIFIER_HASH')
    require(Path(__file__).absolute() == packet / 'public/verify.py', 'SELECTED_VERIFIER')
    require(digest(regular(packet / 'public/control_checks.py')) == final['controls_sha256'], 'CONTROLS_HASH')
    mb = regular(packet / 'MANIFEST.json')
    require(digest(mb) == final['manifest_sha256'], 'MANIFEST_HASH')
    manifest = json.loads(mb)
    require(manifest['pin'] == PIN, 'MANIFEST_PIN')
    expected = manifest['files']
    for key in expected:
        relpath(key)
    for key in manifest['directories']:
        if key != '.':
            relpath(key)
    files, dirs = walk(packet)
    files.pop('MANIFEST.json')
    require(files == expected, 'PAYLOAD_INVENTORY_HASH_MODE')
    require(dirs == manifest['directories'], 'DIRECTORY_INVENTORY_MODE')
    require(digest(regular(packet / 'public/report.md')) == final['public_report_sha256'], 'PUBLIC_REPORT')
    tb = regular(Path(a.canonical_tree))
    require(digest(tb) == TREE, 'EXTERNAL_TREE_HASH')
    require(regular(packet / 'private/context/preprints-tree.json') == tb, 'COPIED_TREE')
    tree = json.loads(tb)
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'TREE_COMPLETENESS')
    bypath = {r['path']: r for r in tree['tree']}
    require(len(bypath) == 13223, 'TREE_UNIQUE')
    sources = json.loads(regular(packet / 'public/source-register.json'))
    require(len(sources) == 199, 'SOURCE_COUNT')
    seen, retained = set(), 0
    for row in sources:
        entry = row['tree_entry']
        path = entry['path']
        require(path not in seen and bypath.get(path) == entry, 'FULL_CANONICAL_RECORD')
        seen.add(path)
        require(entry['type'] == 'blob', 'CANONICAL_TYPE')
        require(row['raw_url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + path, 'PINNED_RAW_URL')
        local = relpath(row['local'])
        require(local == 'private/upstream/' + path, 'SOURCE_LOCAL')
        require(row['bytes'] == entry['size'] and re.fullmatch('[0-9a-f]{64}', row['sha256']), 'SOURCE_METADATA')
        if row['retained']:
            retained += 1
            b = regular(packet / local)
            require(len(b) == entry['size'] and digest(b) == row['sha256'], 'SOURCE_SHA256_SIZE')
            require(hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == entry['sha'], 'GIT_BLOB')
            require(re.findall(r'\\label\{([^}]+)\}', b.decode()) == row['labels_present'], 'LABEL_INVENTORY')
        else:
            require(not (packet / local).exists(), 'REMOVED_SOURCE_PRESENT')
    require(retained == 12, 'RETAINED_COUNT')
    primaries = json.loads(regular(packet / 'public/primary-register.json'))
    require(len(primaries) == 3, 'PRIMARY_COUNT')
    for row in primaries:
        b = regular(packet / relpath(row['pdf_local']))
        require(digest(b) == row['pdf_sha256'] and len(b) == row['bytes'], 'PRIMARY_PDF')
        require(digest(regular(packet / relpath(row['text_local']))) == row['text_sha256'], 'PRIMARY_TEXT')
    history = json.loads(regular(packet / 'public/history-register.json'))
    require(len(history) == 22, 'HISTORY_COUNT')
    for row in history:
        b = regular(packet / relpath(row['local']))
        require(digest(b) == row['sha256'] and len(b) == row['bytes'], 'HISTORY_COPY')
    renders = json.loads(regular(packet / 'private/render/register.json'))
    require(len(renders) == 3, 'RENDER_COUNT')
    for row in renders:
        require(digest(regular(packet / ('private/render/' + row['name'] + '.png'))) == row['sha256'], 'RENDER')
    print(json.dumps({'status': 'INTEGRITY_ONLY', 'payload_files': len(files),
                      'directories_including_root': len(dirs), 'canonical_records': len(sources),
                      'retained_sources': retained, 'removed_sources': len(sources)-retained,
                      'primary_pairs': len(primaries), 'history_copies': len(history),
                      'renders': len(renders), 'final_sha256': a.finalhash,
                      'report_sha256': a.reporthash, 'manifest_sha256': digest(mb)}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as exc:
        print('REJECT: ' + str(exc), file=sys.stderr)
        sys.exit(1)
