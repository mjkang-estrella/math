#!/usr/bin/env python3
"""Read-only byte/provenance verification. No mathematical gates or network."""
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

def require(ok, message):
    if not ok:
        raise ValueError(message)

def regular(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'not a single-link regular file: '+str(path))
    return path.read_bytes()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def unique(items):
    out = {}
    for k, v in items:
        require(k not in out, 'duplicate JSON key')
        out[k] = v
    return out

def decode(data):
    return json.loads(data, object_pairs_hook=unique)

def relative(s):
    require(isinstance(s, str) and s and '\\' not in s, 'invalid relative path')
    p = PurePosixPath(s)
    require(not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and str(p)==s, 'unsafe relative path')
    return s

def inventory(packet):
    require(packet.is_dir() and not packet.is_symlink(), 'packet is not a real directory')
    files, dirs = {}, []
    for base, ds, fs in os.walk(packet, followlinks=False):
        for name in ds:
            p = Path(base)/name
            require(not p.is_symlink(), 'symlink directory')
            dirs.append(p.relative_to(packet).as_posix())
        for name in fs:
            p = Path(base)/name
            b = regular(p)
            files[p.relative_to(packet).as_posix()] = {'sha256': sha(b), 'bytes': len(b)}
    return files, sorted(dirs)

def run(args):
    require(re.fullmatch('[0-9a-f]{64}', args.finalhash) is not None, 'invalid detached FINAL hash')
    require(re.fullmatch('[0-9a-f]{64}', args.reporthash) is not None, 'invalid detached REPORT hash')
    root = Path(args.root)
    require(root.is_dir() and not root.is_symlink(), 'root is not a real directory')
    final_bytes = regular(root/'FINAL.json')
    require(sha(final_bytes)==args.finalhash, 'detached FINAL mismatch')
    final = decode(final_bytes)
    require(final['pin']==PIN and final['status']=='PREFREEZE_NO_NOMINEE', 'wrong archive identity')
    report = regular(root/'REPORT.md')
    require(sha(report)==args.reporthash==final['report_sha256'], 'detached REPORT mismatch')
    manifest_bytes = regular(root/'MANIFEST.json')
    require(sha(manifest_bytes)==final['manifest_sha256'], 'manifest mismatch')
    verifier = regular(root/'packet/public/verify.py')
    require(sha(verifier)==final['verifier_sha256']==sha(regular(Path(__file__))), 'verifier mismatch')
    manifest = decode(manifest_bytes)
    require(manifest['pin']==PIN and manifest['format']==1, 'manifest identity')
    for p in manifest['files']: relative(p)
    for p in manifest['directories']: relative(p)
    require(len(manifest['directories'])==len(set(manifest['directories'])), 'duplicate directory')
    files, dirs = inventory(root/'packet')
    require(set(files)==set(manifest['files']), 'packet file membership mismatch')
    require(dirs==manifest['directories'], 'packet directory membership mismatch')
    require(files==manifest['files'], 'payload bytes mismatch')
    packet = root/'packet'
    external = regular(Path(args.tree))
    require(sha(external)==TREE_HASH, 'external complete tree mismatch')
    tree = decode(external)
    require(tree['truncated'] is False and len(tree['tree'])==13223, 'tree completeness mismatch')
    bypath = {e['path']:e for e in tree['tree']}
    require(len(bypath)==13223, 'duplicate canonical path')
    require(regular(packet/'private/context/sources/preprints-tree.json')==external, 'sealed tree mismatch')
    upstream = decode(regular(packet/'private/context/sources/upstream.json'))
    require(upstream['commit']==PIN, 'upstream pin mismatch')
    sources = decode(regular(packet/'public/source-register.json'))
    seen = set()
    for row in sources:
        require(row['path'] not in seen, 'duplicate source record'); seen.add(row['path'])
        e = bypath[row['path']]
        b = regular(packet/relative(row['local']))
        blob = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(e['type']=='blob' and e['sha']==blob==row['git_blob'], 'canonical source blob mismatch')
        require(sha(b)==row['sha256'] and len(b)==row['bytes'], 'source metadata mismatch')
        require(row['raw_url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+row['path'], 'pinned URL mismatch')
        require(row['labels']==re.findall(r'\\label\{([^}]+)\}',b.decode()), 'source labels mismatch')
    primaries = decode(regular(packet/'public/primary-register.json'))
    successes = 0
    for row in primaries:
        if 'error' in row: continue
        for suffix, key in [('pdf','pdf_sha256'),('txt','text_sha256')]:
            require(sha(regular(packet/relative('private/primary/'+row['key']+'.'+suffix)))==row[key], 'primary mismatch')
        successes += 1
    for row in decode(regular(packet/'public/history-register.json')):
        b = regular(packet/relative(row['local']))
        require(sha(b)==row['sha256'] and len(b)==row['bytes'], 'history mismatch')
    for row in decode(regular(packet/'public/context-register.json')):
        if 'snapshot' in row:
            require(sha(regular(packet/relative(row['snapshot'])))==row['snapshot_sha256'], 'context snapshot mismatch')
    for row in decode(regular(packet/'public/search-register.json')):
        b = regular(packet/relative('private/search/'+row['key']+'.txt'))
        require(sha(b)==row['sha256'] and len(b)==row['bytes'] and len(b.splitlines())==row['lines'], 'search receipt mismatch')
    print(json.dumps({'integrity':'verified','payload_files':len(files),'directories':len(dirs),'canonical_blobs':len(sources),'primary_pairs':successes,'mathematical_gate':None},sort_keys=True))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',required=True)
    parser.add_argument('--tree',required=True)
    parser.add_argument('--finalhash',required=True)
    parser.add_argument('--reporthash',required=True)
    try:
        run(parser.parse_args())
    except (ValueError, KeyError, OSError, TypeError) as error:
        print('REJECT: '+str(error),file=sys.stderr)
        sys.exit(1)
