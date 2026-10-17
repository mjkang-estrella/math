#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only exact-inventory verifier. Supply the manifest digest externally.

Authenticates bytes, including recorded provenance; does not certify mathematics,
primary reading, visual inspection, or an independent review verdict.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

MANIFEST = 'output-manifest.json'
SCHEMA = 'AGM063-manuscript-exact-inventory-v1'


def need(test, message):
    if not test:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def parse(data):
    return json.loads(data, object_pairs_hook=unique)


def safe(name):
    need(isinstance(name, str) and name and '\\' not in name and '\x00' not in name,
         'invalid path')
    p = PurePosixPath(name)
    need(not p.is_absolute() and p.as_posix() == name and
         all(x not in ('.', '..') for x in p.parts), 'noncanonical path: ' + name)
    return name


def digest(value):
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value) is not None


def root_path(path):
    path = Path(os.path.abspath(path))
    for part in [path, *path.parents]:
        need(not part.is_symlink(), 'symlink in root ancestry')
    need(path.is_dir(), 'root is not a directory')
    return path


def inventory(root):
    files, directories = {}, []
    for folder, ds, fs in os.walk(root, followlinks=False):
        for name in ds + fs:
            p = Path(folder) / name
            rel = safe(p.relative_to(root).as_posix())
            st = p.lstat()
            need(not stat.S_ISLNK(st.st_mode), 'symlink: ' + rel)
            if stat.S_ISDIR(st.st_mode):
                directories.append(rel)
            else:
                need(stat.S_ISREG(st.st_mode), 'nonregular file: ' + rel)
                need(st.st_nlink == 1, 'hard-linked file: ' + rel)
                files[rel] = st.st_size
    return files, sorted(directories)


def verify(root, anchor):
    root = root_path(root)
    need(digest(anchor), 'invalid external anchor')
    actual, dirs = inventory(root)
    need(MANIFEST in actual, 'manifest missing')
    raw = (root / MANIFEST).read_bytes()
    need(sha(raw) == anchor, 'external anchor mismatch')
    m = parse(raw)
    need(set(m) == {'schema', 'stage', 'files', 'directories', 'limits'}, 'manifest keys')
    need(m['schema'] == SCHEMA, 'schema')
    need(m['stage'] in ('preseal-control', 'final'), 'stage')
    need(m['limits'] == 'Integrity only; no mathematical or independent-review verdict.', 'limits')
    expected = {}
    need(isinstance(m['files'], list) and isinstance(m['directories'], list), 'inventory types')
    for row in m['files']:
        need(isinstance(row, dict) and set(row) == {'path', 'bytes', 'sha256'}, 'file record')
        name = safe(row['path'])
        need(name != MANIFEST and name not in expected, 'duplicate/self payload')
        need(type(row['bytes']) is int and row['bytes'] >= 0 and digest(row['sha256']), 'size/digest')
        expected[name] = row
    wanted_dirs = [safe(x) for x in m['directories']]
    need(wanted_dirs == sorted(set(wanted_dirs)), 'directory inventory order/duplicates')
    need(list(expected) == sorted(expected), 'file inventory order')
    need(set(actual) == set(expected) | {MANIFEST}, 'exact file membership')
    need(dirs == wanted_dirs, 'exact directory membership')
    for name, row in expected.items():
        data = (root / name).read_bytes()
        need(len(data) == row['bytes'] and sha(data) == row['sha256'], 'payload mismatch: ' + name)
    # Binding checks authenticate the exact source/PDF/page relationship claimed
    # by the author. Their presence is not a machine proof of visual inspection.
    if m['stage'] == 'final':
        build = parse((root / 'checks/build-receipt.json').read_bytes())
        visual = parse((root / 'checks/visual-review.json').read_bytes())
        for key, name in [('source_sha256', 'main.tex'), ('formal_support_sha256', 'formal-support.tex'),
                          ('pdf_sha256', 'output/pdf/advanced-mukai-classification.pdf')]:
            need(build[key] == expected[name]['sha256'], 'build binding: ' + key)
        need(visual['status'] == 'FINAL_ALL_PAGES_VISUALLY_INSPECTED', 'final visual status')
        need(visual['pdf_sha256'] == build['pdf_sha256'], 'visual PDF binding')
        count = build['pdf_pages']
        need(type(count) is int and count > 0, 'page count')
        need(visual['page_count'] == count == build['rendered_pages'], 'page count consistency')
        need([p['page'] for p in visual['pages']] == list(range(1, count + 1)), 'page inventory')
        for row in visual['pages']:
            name = safe(row['path'])
            need(row['visually_inspected'] is True and expected[name]['sha256'] == row['sha256'],
                 'visual page binding')
        need({p['path'] for p in visual['pages']} ==
             {p for p in expected if p.startswith('checks/pages/')}, 'exact rendered pages')
        for key in ('overfull_boxes', 'undefined', 'rerun'):
            need(build['log_findings'][key] == 0, 'unresolved build finding: ' + key)
        status = parse((root / 'final-checkpoint.json').read_bytes())
        need(status['full_AGM063_theorem_formalized'] is False, 'formal overclaim')
        need(status['formal_review_adopted_by_root'] is True, 'formal adoption pending')
        for row in status['external_inputs']:
            name = safe(row['snapshot'])
            need(digest(row['sha256']) and expected[name]['sha256'] == row['sha256'], 'input anchor')
        adoption = parse((root / 'private/inputs/agm063-parent/formal-review-adoption.json').read_bytes())
        coverage = parse((root / 'formal-coverage.json').read_bytes())
        review_name = 'private/inputs/agm063-formal-review-r1/review-manifest.json'
        implementation_name = 'private/inputs/agm063-formal-v1/output-manifest.json'
        need(adoption['status'] == 'ADOPTED_PASS_SCOPED_SUPPORT', 'root adoption status')
        need(adoption['review_manifest_sha256'] == expected[review_name]['sha256'] ==
             coverage['review_manifest_sha256'], 'formal review anchor binding')
        need(adoption['implementation_manifest_sha256'] == expected[implementation_name]['sha256'] ==
             coverage['implementation_manifest_sha256'], 'formal implementation anchor binding')
        need(coverage['full_AGM063_theorem_formalized'] is False, 'coverage overclaim')
    return {'status': 'PASS_INTEGRITY_ONLY', 'stage': m['stage'], 'files': len(expected),
            'directories': len(dirs), 'manifest_sha256': anchor, 'writes': 0,
            'mathematics_verified': False}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--root', type=Path, default=Path(__file__).absolute().parent)
    a = ap.parse_args()
    print(json.dumps(verify(a.root, a.anchor), sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print('INTEGRITY_REJECT: ' + str(exc))
        raise SystemExit(1)
