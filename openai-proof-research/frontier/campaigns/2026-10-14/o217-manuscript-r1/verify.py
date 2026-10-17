#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Authenticate exact manuscript bytes and QA bindings; not a proof checker."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    d = {}
    for k, v in pairs:
        need(k not in d, 'duplicate JSON key')
        d[k] = v
    return d


def read(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique)


def safe(name):
    need(isinstance(name, str) and name and '\\' not in name, 'invalid path')
    p = PurePosixPath(name)
    need(not p.is_absolute() and p.as_posix() == name, 'noncanonical path')
    need(all(s not in ('.', '..', '') for s in p.parts), 'unsafe path')
    return name


def verify(root, anchor):
    need(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'invalid anchor')
    need(root.is_dir() and not root.is_symlink(), 'invalid root')
    manifest = root / 'output-manifest.json'
    need(not manifest.is_symlink(), 'manifest symlink')
    need(sha(manifest.read_bytes()) == anchor, 'external anchor mismatch')
    m = read(manifest)
    need(m['schema'] == 'O217-manuscript-r1', 'schema')
    need(m['full_theorem_formalized'] is False, 'formal scope')
    need(m['independent_manuscript_verdict'] is False, 'authorship role')
    expected = {}
    for row in m['files']:
        name = safe(row['path'])
        need(name not in expected and name != 'output-manifest.json', 'duplicate/self file')
        expected[name] = row
    expected_dirs = [safe(s) for s in m['directories']]
    need(len(set(expected_dirs)) == len(expected_dirs), 'duplicate directory')
    files, dirs = set(), set()
    for folder, ds, fs in os.walk(root, followlinks=False):
        for name in ds + fs:
            p = Path(folder) / name
            rel = safe(p.relative_to(root).as_posix())
            mode = p.lstat().st_mode
            need(not stat.S_ISLNK(mode), 'symlink: ' + rel)
            if stat.S_ISDIR(mode):
                dirs.add(rel)
            else:
                need(stat.S_ISREG(mode), 'nonregular file: ' + rel)
                files.add(rel)
    need(files == set(expected) | {'output-manifest.json'}, 'file inventory')
    need(dirs == set(expected_dirs), 'directory inventory')
    for name, row in expected.items():
        data = (root / name).read_bytes()
        need(len(data) == row['bytes'] and sha(data) == row['sha256'], 'payload hash: ' + name)
    build = read(root / 'checks/build-receipt.json')
    visual = read(root / 'checks/visual-review.json')
    pdf = root / 'output/pdf/fourth-moment-sk-comparison.pdf'
    need(build['pdf_sha256'] == visual['pdf_sha256'] == sha(pdf.read_bytes()), 'PDF binding')
    for path, key in [('main.tex', 'source_sha256'), ('formal-support.tex', 'formal_support_sha256')]:
        need(build[key] == sha((root / path).read_bytes()), 'source binding')
    need(visual['main_sha256'] == build['source_sha256'], 'visual main binding')
    need(visual['formal_support_sha256'] == build['formal_support_sha256'], 'visual support binding')
    need(visual['status'] == 'ALL_FINAL_PAGES_INSPECTED', 'visual status')
    n = build['pdf_pages']
    need(n == build['rendered_pages'] == len(visual['pages']), 'page count')
    need([r['page'] for r in visual['pages']] == list(range(1, n + 1)), 'page sequence')
    for row in visual['pages']:
        need(sha((root / safe(row['path'])).read_bytes()) == row['sha256'], 'page image binding')
    for k in ['overfull_boxes', 'undefined', 'rerun']:
        need(build['log_findings'][k] == 0, 'compiler finding: ' + k)
    replay = read(root / 'checks/rebuild-comparison.json')
    need(replay['identical_pdf'] is True and replay['identical_page_images'] is True, 'rebuild equality')
    need(replay['pdf_sha256'] == build['pdf_sha256'], 'rebuild binding')
    deps = read(root / 'dependency-anchors.json')
    need(isinstance(deps['formal_implementation'], dict), 'missing formal identity')
    need(isinstance(deps['formal_audit'], dict), 'missing audit identity')
    return dict(result='PASS_INTEGRITY_ONLY', payloads=len(expected), pages=n,
                writes=0, full_theorem_formalized=False, independent_manuscript_verdict=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    a = ap.parse_args()
    print(json.dumps(verify(a.root.absolute(), a.anchor), sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print('INTEGRITY_REJECT: ' + str(exc))
        raise SystemExit(1)
