#!/usr/bin/env python3
"""Offline, read-only artifact verifier. Not a mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
SCOPE = '6e39d59e65aecf9fc8710244c7eccbe7964e38af10287ad173663585539d790a'
PREFREEZE = 'd58e6e8ae9645a2565237b7d606cd41ac5acfa3b5580209b7f9e2756257e623e'
SEARCH = {
    'hits.json': '519917adf4639057d9fcf0cafc1c442b926a445cf17958d9cc76282dc28b1f32',
    'inventory.json': '6b5e4d0097ff1ee217f1c915de78fd45610f37a612d29ee1be5afb6bad93db9b',
    'receipt.json': 'dc1538ebda4c686cef3475bd52a9c5a6989b17969ce91c1f6bb4739ccf7dfd4b',
}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def read_json(path):
    return json.loads(path.read_bytes())

def audit(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        bad_mode = isinstance(mode, str) and any(c in mode for c in 'wax+')
        bad_flags = isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)
        if bad_mode or bad_flags:
            raise PermissionError('read-only audit: write denied')
    if event.startswith(('socket.', 'subprocess.')) or event in {
        'os.remove', 'os.rename', 'os.mkdir', 'os.rmdir', 'os.symlink',
        'os.link', 'os.chmod', 'os.chown', 'os.truncate', 'os.system',
        'os.utime', 'os.setxattr', 'os.removexattr'}:
        raise PermissionError('read-only audit: mutation/network/process denied')

def inventory(packet):
    files, dirs = {}, ['.']
    for base, ds, fs in os.walk(packet, followlinks=False):
        for name in ds + fs:
            q = Path(base) / name
            require(not q.is_symlink(), 'symlink: ' + str(q))
            rel = q.relative_to(packet).as_posix()
            if q.is_dir():
                dirs.append(rel)
            elif q.is_file():
                if rel != 'MANIFEST.json':
                    b = q.read_bytes()
                    files[rel] = {'bytes': len(b), 'sha256': digest(b)}
            else:
                raise ValueError('nonregular payload: ' + rel)
    return dict(sorted(files.items())), sorted(dirs)

def verify(root, final_hash, report_hash):
    for name in ('packet', 'FINAL.json', 'REPORT.md'):
        require(not (root/name).is_symlink(), 'root symlink')
    require(digest((root/'FINAL.json').read_bytes()) == final_hash, 'detached FINAL mismatch')
    require(digest((root/'REPORT.md').read_bytes()) == report_hash, 'detached report mismatch')
    final = read_json(root/'FINAL.json')
    require(final['pin'] == PIN and final['status'] == 'AUTHOR_FULL_PROOF_NO_INDEPENDENT_GATES', 'status/pin')
    require(final['scope_sha256'] == SCOPE and final['prefreeze_sha256'] == PREFREEZE, 'frozen anchor')
    packet = root/'packet'
    require(digest((packet/'MANIFEST.json').read_bytes()) == final['manifest_sha256'], 'manifest anchor')
    manifest = read_json(packet/'MANIFEST.json')
    files, dirs = inventory(packet)
    require(files == manifest['files'] and dirs == manifest['directories'], 'exact payload inventory')
    require(digest((packet/'public/frozen-scope.md').read_bytes()) == SCOPE, 'scope changed')
    require(digest((packet/'public/prefreeze.md').read_bytes()) == PREFREEZE, 'prefreeze changed')
    freeze = read_json(packet/'public/freeze.json')
    require(freeze['frozen-scope.md'] == SCOPE and freeze['prefreeze.md'] == PREFREEZE, 'freeze receipt')
    for name, value in final['proof_files'].items():
        require(name in {'proof.md', 'boundary-calculation.md', 'transport-calculation.md'}, 'proof file name')
        require(digest((packet/'public'/name).read_bytes()) == value, 'proof anchor')
    require(len(final['proof_files']) == 3, 'proof components')
    records = final['records']
    require(set(records) == {'consistency-check.md', 'report.md', 'reading-limits.md', 'verify.py'}, 'record names')
    for name, value in records.items():
        require(digest((packet/'public'/name).read_bytes()) == value, 'record anchor')
    runner = final['runner']
    require(runner['initial'].startswith('GPT-6 Astra') and runner['resumed'] == 'Factory Droid (Opus 5.5, high)', 'runner record')
    require(final['verdicts'] == {'correctness': None, 'contribution': None, 'count': None}, 'no self-verdicts')
    require(SCOPE in (packet/'public/proof.md').read_text(), 'scope reference')
    tree_path = packet/'private/context/preprints-tree.json'
    require(digest(tree_path.read_bytes()) == TREE, 'complete tree anchor')
    tree = read_json(tree_path)
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'complete tree contract')
    canonical = {x['path']: x for x in tree['tree']}
    require(len(canonical) == 13223, 'duplicate canonical path')
    require(read_json(packet/'private/context/upstream.json')['commit'] == PIN, 'upstream pin')
    path_records = 0
    for f in (packet/'private/upstream').glob('*-paths.json'):
        for row in read_json(f):
            require(canonical.get(row['path']) == row, 'full canonical path metadata')
            path_records += 1
    rows = read_json(packet/'private/upstream/register.json')
    require(len(rows) == 41 and len({x['canonical']['path'] for x in rows}) == 41, 'acquisition register')
    retained = 0
    for row in rows:
        c = row['canonical']
        require(canonical.get(c['path']) == c, 'full canonical acquisition metadata')
        require(row['url'] == 'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+c['path'], 'raw URL')
        q = packet/row['local']
        require(q.is_relative_to(packet/'private/upstream'), 'source local path')
        if row['retained']:
            retained += 1
            b = q.read_bytes()
            require(len(b) == c['size'] and digest(b) == row['sha256'], 'source bytes')
            require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest() == c['sha'], 'Git blob')
            require(re.findall(r'\\label\{([^}]+)\}', b.decode()) == row['labels'], 'source labels')
        else:
            require(not q.exists() and 'unread' in row['read'], 'removed source contract')
    require(retained == 11, 'retained source count')
    primary_count = 0
    for register in (packet/'private/primary').glob('register*.json'):
        for row in read_json(register):
            name = row['id']
            require(re.fullmatch(r'\d{4}\.\d{4,5}v\d+', name) is not None, 'primary version')
            require(row['url'] == 'https://arxiv.org/pdf/'+name, 'primary URL')
            require(row['extraction_exit'] == 0 and row['stderr'] == '', 'extraction receipt')
            for ext, key in [('pdf', 'pdf_sha256'), ('txt', 'text_sha256')]:
                b = (packet/'private/primary'/(name+'.'+ext)).read_bytes()
                require(digest(b) == row[key], 'primary pair bytes')
                if ext == 'pdf':
                    require(b.startswith(b'%PDF'), 'PDF magic')
            primary_count += 1
    require(primary_count == 6, 'primary count')
    for register in ['private/history/register.json', 'private/context/findings-register.json']:
        for row in read_json(packet/register):
            require(digest((packet/row['local']).read_bytes()) == row['sha256'], 'copied history/context bytes')
    search = packet/'private/search/broad-prefreeze'
    for name, value in SEARCH.items():
        require(digest((search/name).read_bytes()) == value, 'search evidence anchor')
    receipt = read_json(search/'receipt.json')
    inv = read_json(search/'inventory.json')
    hits = read_json(search/'hits.json')
    require(receipt['no_size_cutoff'] is True and receipt['errors'] == [], 'search contract')
    require(len(inv) == receipt['files'] and sum(x[1] for x in inv) == receipt['bytes'], 'search inventory counts')
    require(max(x[1] for x in inv) == receipt['largest'] and len(hits) == receipt['hits'], 'search sizes/hits')
    paths = {x[0] for x in inv}
    pattern = re.compile(receipt['pattern'], re.I)
    require(all(x['path'] in paths and x['line'] > 0 and pattern.search(x['text']) for x in hits), 'search hit records')
    return {'artifact_integrity_only': True, 'payloads': len(files), 'directories': len(dirs),
            'canonical_acquisitions': len(rows), 'retained_sources': retained,
            'canonical_path_metadata': path_records, 'primary_pairs': primary_count,
            'frozen_scope_unchanged': True, 'independent_mathematical_gate': False}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--final-hash', required=True)
    parser.add_argument('--report-hash', required=True)
    parser.add_argument('--audit-probe', choices=['write', 'network'])
    args = parser.parse_args()
    require(re.fullmatch('[0-9a-f]{64}', args.final_hash) is not None, 'invalid detached FINAL')
    require(re.fullmatch('[0-9a-f]{64}', args.report_hash) is not None, 'invalid detached report')
    sys.addaudithook(audit)
    if args.audit_probe == 'write':
        (args.root/'forbidden-write').write_text('denied')
    if args.audit_probe == 'network':
        import socket
        socket.socket()
    print(json.dumps(verify(args.root.resolve(), args.final_hash, args.report_hash), sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('REJECT: '+str(error), file=sys.stderr)
        sys.exit(2)
