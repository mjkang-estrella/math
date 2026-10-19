#!/usr/bin/env python3
"""Read-only local evidence integrity verifier. Not a mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result

def parse(data):
    return json.loads(data, object_pairs_hook=pairs)

def safe(relative):
    p = PurePosixPath(relative)
    require(isinstance(relative, str) and relative and not p.is_absolute()
            and str(p) == relative and all(x not in ('', '.', '..') for x in p.parts)
            and '\\' not in relative, 'unsafe relative path')
    return relative

def inventory(root):
    require(not root.is_symlink() and root.is_dir(), 'invalid packet root')
    files, dirs = {}, []
    for current, directory_names, file_names in os.walk(root, followlinks=False):
        for name in directory_names + file_names:
            path = Path(current) / name
            mode = path.lstat().st_mode
            relative = path.relative_to(root).as_posix()
            safe(relative)
            require(not stat.S_ISLNK(mode), 'symlink: ' + relative)
            if stat.S_ISDIR(mode):
                dirs.append(relative)
            else:
                require(stat.S_ISREG(mode), 'special file: ' + relative)
                data = path.read_bytes()
                files[relative] = {'sha256': sha(data), 'bytes': len(data)}
    return files, sorted(dirs)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--expected-manifest-sha256', required=True,
                        help='Detached trusted final hash; never read from packet')
    parser.add_argument('--tree', type=Path, required=True,
                        help='Exact complete external preprints-tree.json')
    args = parser.parse_args()
    require(re.fullmatch('[0-9a-f]{64}', args.expected_manifest_sha256), 'bad anchor format')
    root = args.packet.absolute()
    files, dirs = inventory(root)
    require('manifest.json' in files, 'missing manifest')
    require(files['manifest.json']['sha256'] == args.expected_manifest_sha256,
            'detached manifest anchor mismatch')
    manifest = parse((root / 'manifest.json').read_bytes())
    require(manifest['schema'] == 'r112-evidence-v1' and manifest['pin'] == PIN, 'identity mismatch')
    require(manifest['status'] == 'pre-freeze-screening-no-nominee', 'status mismatch')
    expected = manifest['files']
    require(isinstance(expected, dict), 'bad inventory')
    for relative in expected:
        safe(relative)
    del files['manifest.json']
    require(files == expected, 'payload inventory/hash/size mismatch')
    require(dirs == manifest['directories'], 'directory inventory mismatch')
    require(not args.tree.is_symlink() and args.tree.is_file(), 'invalid complete tree')
    tree_bytes = args.tree.read_bytes()
    require(sha(tree_bytes) == manifest['external_complete_tree']['sha256'], 'tree anchor mismatch')
    tree = parse(tree_bytes)
    require(tree.get('truncated') is False and len(tree['tree']) == 13223, 'incomplete tree')
    entries = {row['path']: row for row in tree['tree']}
    require(len(entries) == 13223, 'duplicate tree paths')
    require(sum(row['type'] == 'blob' for row in tree['tree']) == 10373, 'tree blob count')
    receipts = parse((root / 'private/upstream-receipts.json').read_bytes())
    require(len(receipts) == manifest['canonical_blob_count'], 'receipt count')
    seen = set()
    for receipt in receipts:
        relative = safe(receipt['local'])
        path = receipt['path']
        require(path not in seen, 'duplicate canonical receipt')
        seen.add(path)
        require(relative == 'private/upstream/' + path, 'canonical local path')
        data = (root / relative).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(entries[path]['type'] == 'blob' and entries[path]['sha'] == blob
                and receipt['git_blob'] == blob, 'canonical Git blob mismatch')
        require(receipt['sha256'] == sha(data) and receipt['bytes'] == len(data), 'receipt bytes')
        require(receipt['raw_url'] == 'https://raw.githubusercontent.com/openai/math/'
                + PIN + '/' + path, 'unpinned raw URL')
    primaries = parse((root / 'private/primary/receipts.json').read_bytes())
    require(len(primaries) == manifest['primary_pdf_count'], 'primary count')
    seen = set()
    for receipt in primaries:
        name = safe(receipt['name'])
        require('/' not in name and name not in seen, 'invalid primary name')
        seen.add(name)
        pdf = (root / 'private/primary' / (name + '.pdf')).read_bytes()
        text = (root / 'private/primary' / (name + '.txt')).read_bytes()
        require(sha(pdf) == receipt['sha256'] and len(pdf) == receipt['bytes'], 'primary PDF')
        require(sha(text) == receipt['text_sha256'], 'primary extracted text')
    print(json.dumps({'integrity_only': True, 'payloads': len(files),
                      'canonical_blobs': len(receipts), 'primary_pdfs': len(primaries),
                      'complete_tree_entries': 13223,
                      'detached_manifest_sha256': args.expected_manifest_sha256}, sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as error:
        print('INTEGRITY REJECT: ' + str(error), file=sys.stderr)
        sys.exit(1)
