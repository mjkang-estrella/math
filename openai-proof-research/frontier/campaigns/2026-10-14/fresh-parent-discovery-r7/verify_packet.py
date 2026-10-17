#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only packet identity check; requires externally supplied manifest SHA256."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

def digest(b):
    return hashlib.sha256(b).hexdigest()

def check(ok, message):
    if not ok:
        raise SystemExit('FAIL: ' + message)

def canonical(name):
    p = PurePosixPath(name)
    check(not p.is_absolute() and '..' not in p.parts and str(p) == name and name != '.', 'noncanonical path')
    return p

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--manifest-sha256', required=True)
a = p.parse_args()
root = Path(__file__).resolve().parent
check(not (root/'manifest.json').is_symlink(), 'manifest symlink')
data = (root/'manifest.json').read_bytes()
check(digest(data) == a.manifest_sha256, 'external manifest anchor')
m = json.loads(data)
rows = m['files']
names = [r['path'] for r in rows]
check(len(names) == len(set(names)), 'duplicate path')
check('manifest.json' not in names, 'self inclusion')
expected_dirs = set()
for name in names:
    path = canonical(name)
    expected_dirs.update(str(q) for q in path.parents if str(q) != '.')
all_paths = list(root.rglob('*'))
check(not any(q.is_symlink() for q in all_paths), 'symlink')
check({q.relative_to(root).as_posix() for q in all_paths if q.is_file()} == set(names)|{'manifest.json'}, 'file membership')
check({q.relative_to(root).as_posix() for q in all_paths if q.is_dir()} == expected_dirs, 'directory membership')
for row in rows:
    b = (root/row['path']).read_bytes()
    check(len(b) == row['bytes'] and digest(b) == row['sha256'], 'payload '+row['path'])
repo = root.parents[3]
b = (repo/'sources/preprints-tree.json').read_bytes()
check(digest(b) == m['catalog_sha256'], 'complete catalog identity')
t = json.loads(b)
check(t['truncated'] is False, 'truncated catalog')
blobs = {q['path']:q['sha'] for q in t['tree'] if q['type']=='blob'}
sources = json.loads((root/'source-receipt.json').read_text())
check(len({q['local'] for q in sources}) == len(sources), 'duplicate local source path')
for row in sources:
    canonical(row['local'])
    b = (root/row['local']).read_bytes()
    check(len(b)==row['bytes'] and digest(b)==row['sha256'], 'source SHA')
    gh = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    check(gh == row['git_blob'] == blobs[row['path']], 'source Git blob')
    check('/'+m['pin']+'/' in row['url'], 'source URL pin')
primary = json.loads((root/'private/primary-receipts.json').read_text())
for row in primary:
    canonical(row['name'])
    b = (root/'private'/(row['name']+'.pdf')).read_bytes()
    check(len(b)==row['pdf_bytes'] and digest(b)==row['pdf_sha256'], 'primary PDF')
    check(digest((root/'private'/(row['name']+'.txt')).read_bytes())==row['text_sha256'], 'primary text')
print(json.dumps({'status':'PASS_IDENTITY_ONLY','payloads':len(rows),'source_blobs':len(sources),'primary_pdfs':len(primary),'frozen_target':False,'counted':False},sort_keys=True))
