#!/usr/bin/env python3
"""Read-only byte/provenance verifier. This is not a mathematical verifier."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREEHASH = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_regular(path):
    s = path.lstat()
    need(stat.S_ISREG(s.st_mode), 'not a regular file: ' + str(path))
    need(s.st_nlink == 1, 'hard link: ' + str(path))
    return path.read_bytes()


def pairs(items):
    d = {}
    for k, v in items:
        need(k not in d, 'duplicate JSON key: ' + k)
        d[k] = v
    return d


def parse(data):
    return json.loads(data, object_pairs_hook=pairs)


def safe(s):
    need(isinstance(s, str) and s and '\\' not in s, 'invalid path')
    p = PurePosixPath(s)
    need(not p.is_absolute() and all(x not in ('', '.', '..') for x in s.split('/')), 'unsafe path: ' + s)
    need(str(p) == s, 'noncanonical path: ' + s)
    return s


def inventory(base):
    need(stat.S_ISDIR(base.lstat().st_mode), 'packet is not an ordinary directory')
    files, dirs = {}, {'.': stat.S_IMODE(base.lstat().st_mode)}
    for parent, ds, fs in os.walk(base, followlinks=False):
        for name in ds:
            p = Path(parent) / name
            s = p.lstat()
            need(stat.S_ISDIR(s.st_mode), 'non-directory/symlink in directory list: ' + str(p))
            dirs[p.relative_to(base).as_posix()] = stat.S_IMODE(s.st_mode)
        for name in fs:
            p = Path(parent) / name
            b = read_regular(p)
            files[p.relative_to(base).as_posix()] = {'sha256': sha(b), 'bytes': len(b), 'mode': stat.S_IMODE(p.lstat().st_mode)}
    return files, dirs


def verify(a):
    for label, h in [('finalhash', a.finalhash), ('reporthash', a.reporthash)]:
        need(re.fullmatch('[0-9a-f]{64}', h) is not None, 'invalid external ' + label)
    root = Path(a.root).absolute()
    need(stat.S_ISDIR(root.lstat().st_mode), 'root not an ordinary directory')
    fb = read_regular(root / 'FINAL.json')
    need(sha(fb) == a.finalhash, 'external FINAL hash mismatch')
    final = parse(fb)
    need(set(final) == {'format','pin','manifest_sha256','report_path','report_sha256','tree_sha256','status'}, 'FINAL schema')
    need(final['format'] == 1 and final['pin'] == PIN and final['status'] == 'PREFREEZE_NO_NOMINEE', 'FINAL scope')
    need(final['report_path'] == 'public/report.md', 'report path')
    need(final['report_sha256'] == a.reporthash, 'external report hash mismatch')
    need(final['tree_sha256'] == TREEHASH, 'tree anchor')
    mb = read_regular(root / 'MANIFEST.json')
    need(sha(mb) == final['manifest_sha256'], 'manifest hash mismatch')
    manifest = parse(mb)
    need(set(manifest) == {'format','pin','files','directories'}, 'manifest schema')
    need(manifest['format'] == 1 and manifest['pin'] == PIN, 'manifest scope')
    expected = {}
    for item in manifest['files']:
        need(set(item) == {'path','sha256','bytes','mode'}, 'file record schema')
        p = safe(item['path'])
        need(p not in expected, 'duplicate manifest file')
        expected[p] = {k: item[k] for k in ('sha256','bytes','mode')}
    need(list(expected) == sorted(expected), 'file records not sorted')
    dirs = {}
    for item in manifest['directories']:
        need(set(item) == {'path','mode'}, 'directory schema')
        p = item['path']
        if p != '.': safe(p)
        need(p not in dirs, 'duplicate directory')
        dirs[p] = item['mode']
    need(list(dirs) == sorted(dirs), 'directory records not sorted')
    packet = root / 'packet'
    actual, actualdirs = inventory(packet)
    need(actual == expected, 'packet file inventory/hash/mode mismatch')
    need(actualdirs == dirs, 'packet directory inventory/mode mismatch')
    need(actual['public/report.md']['sha256'] == a.reporthash, 'report payload mismatch')
    tb = read_regular(Path(a.tree))
    need(sha(tb) == TREEHASH, 'complete tree bytes mismatch')
    tree = parse(tb)
    need(tree['truncated'] is False and len(tree['tree']) == 13223, 'incomplete tree')
    idx = {e['path']: e for e in tree['tree']}
    need(len(idx) == 13223, 'duplicate canonical tree path')
    need(sum(e['type'] == 'blob' for e in idx.values()) == 10373, 'tree blob count')
    need(sum(e['type'] == 'tree' for e in idx.values()) == 2850, 'tree directory count')
    receipt = parse(read_regular(packet / 'public/tree-receipt.json'))
    need(receipt['sha256'] == TREEHASH and receipt['tree_sha'] == tree['sha'], 'tree receipt binding')
    need(receipt['entry_count'] == 13223 and receipt['blob_count'] == 10373 and receipt['tree_count'] == 2850 and receipt['truncated'] is False and receipt['pin'] == PIN, 'tree receipt counts')
    sources = parse(read_regular(packet / 'public/source-register.json'))
    seen = set()
    selected = []
    for r in sources:
        p = safe(r['path']); cp = safe(r['canonical_path'])
        need(p.startswith('private/upstream/') and cp not in seen, 'source location/duplicate')
        seen.add(cp)
        e = idx[cp]; selected.append(e)
        need(e['type'] == 'blob' and e['sha'] == r['git_blob'], 'canonical blob mismatch')
        need(r['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + cp, 'pinned URL mismatch')
        b = read_regular(packet / p)
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        need(blob == r['git_blob'] and sha(b) == r['sha256'] and len(b) == r['bytes'], 'source bytes mismatch')
    need(receipt['selected_entries'] == selected, 'selected canonical entries mismatch')
    need({p for p in actual if p.startswith('private/upstream/')} == {r['path'] for r in sources}, 'unregistered upstream file')
    context = parse(read_regular(packet / 'public/context-receipts.json'))
    contexts = {}
    for r in context:
        cp = safe(r['path'])
        need(cp not in contexts, 'duplicate context reference')
        contexts[cp] = r
    for p in actual:
        if p.startswith('private/history/'):
            cp = p[len('private/history/'):]
            need(cp in contexts, 'unregistered historical copy')
            need(actual[p]['sha256'] == contexts[cp]['sha256'] and actual[p]['bytes'] == contexts[cp]['bytes'], 'historical copy binding')
    primary = parse(read_regular(packet / 'public/primary-register.json'))
    primarypaths = set(); successes = failures = 0
    for r in primary:
        if r.get('status') == 'failed':
            need(r['name'] == 'hutchcroft-1904.05804v3' and '404' in r['error'], 'unrecognized primary failure')
            failures += 1
            continue
        name = r.get('name', r.get('id'))
        pp = r.get('pdf_path', 'private/primary/' + name + '.pdf')
        tp = r.get('text_path', 'private/primary/' + name + '.txt')
        for p, key in [(pp,'pdf_sha256'),(tp,'text_sha256')]:
            safe(p)
            need(p.startswith('private/primary/') and p not in primarypaths, 'primary path/duplicate')
            primarypaths.add(p)
            need(sha(read_regular(packet / p)) == r[key], 'primary bytes mismatch')
        need(re.fullmatch(r'https://arxiv.org/pdf/[0-9]{4}\.[0-9]{4,5}v[0-9]+',r['url']) is not None, 'unversioned primary URL')
        successes += 1
    need(successes == 4 and failures == 1, 'primary access counts')
    need({p for p in actual if p.startswith('private/primary/')} == primarypaths, 'unregistered primary')
    return {'status':'BYTE_IDENTITY_ONLY','files':len(actual),'directories':len(actualdirs),'canonical_blobs':len(sources),'primary_pairs':successes,'recorded_access_failures':failures,'final_sha256':a.finalhash,'manifest_sha256':sha(mb),'report_sha256':a.reporthash,'mathematical_gate':False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True)
    p.add_argument('--finalhash', required=True, help='Detached trusted SHA256; never inferred from the packet')
    p.add_argument('--reporthash', required=True, help='Detached trusted report SHA256')
    p.add_argument('--tree', required=True, help='Complete preprints-tree.json (read only)')
    a = p.parse_args()
    try:
        print(json.dumps(verify(a), sort_keys=True))
    except (ValueError, KeyError, TypeError, OSError) as e:
        print('REJECT: ' + str(e), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
