#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only manuscript byte/identity check, not mathematical verification.
The path/JSON safeguards follow this author's CM275 packet verifier; manuscript
build, reviewed-input, source-contract and page-identity checks are added here.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    result = {}
    for k, v in pairs:
        need(k not in result, 'duplicate JSON key')
        result[k] = v
    return result


def parse(data):
    return json.loads(data, object_pairs_hook=unique)


def name(s):
    need(isinstance(s, str) and s and '\\' not in s, 'invalid path')
    p = PurePosixPath(s)
    need(not p.is_absolute() and p.as_posix() == s, 'noncanonical path')
    need(all(x not in ('', '.', '..', '__pycache__') for x in p.parts), 'unsafe path')
    need(not s.endswith(('.pyc', '.pyo')), 'bytecode forbidden')
    return s


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    args = ap.parse_args()
    need(re.fullmatch('[0-9a-f]{64}', args.anchor) is not None, 'invalid anchor')
    root = Path(__file__).absolute().parents[1]
    need(not root.is_symlink(), 'root symlink')
    seal = root / 'manifest.json'
    need(not seal.is_symlink(), 'manifest symlink')
    raw = seal.read_bytes()
    need(sha(raw) == args.anchor, 'external anchor mismatch')
    m = parse(raw)
    need(m['schema'] == 'CM275-manuscript-r1-v1', 'schema mismatch')
    expected = {}
    for row in m['files']:
        n = name(row['path'])
        need(n not in expected and n != 'manifest.json', 'duplicate/self payload')
        expected[n] = row
    dirs = [name(x) for x in m['directories']]
    need(len(dirs) == len(set(dirs)), 'duplicate directory')
    found_files, found_dirs = set(), set()
    for folder, subdirs, fs in os.walk(root, followlinks=False):
        for n in subdirs + fs:
            p = Path(folder) / n
            rel = name(p.relative_to(root).as_posix())
            mode = p.lstat().st_mode
            need(not stat.S_ISLNK(mode), 'symlink')
            if stat.S_ISDIR(mode):
                found_dirs.add(rel)
            else:
                need(stat.S_ISREG(mode), 'nonregular file')
                found_files.add(rel)
    need(found_files == set(expected) | {'manifest.json'}, 'file membership')
    need(found_dirs == set(dirs), 'directory membership')
    for n, row in expected.items():
        data = (root / n).read_bytes()
        need(len(data) == row['bytes'] and sha(data) == row['sha256'], 'payload: ' + n)
    read = lambda n: parse((root / name(n)).read_bytes())
    inputs = read('input-receipt.json')
    for rec in inputs['snapshots']:
        data = (root / name(rec['local'])).read_bytes()
        need(len(data) == rec['bytes'] and sha(data) == rec['sha256'], 'input snapshot')
    for role in ['author', 'proof', 'contribution']:
        raw = (root / ('inputs/' + role + '-output-manifest.json')).read_bytes()
        need(sha(raw) == inputs['external_anchors'][role], 'dependency anchor: ' + role)
    author = read('inputs/author-output-manifest.json')
    amap = {x['path']: x['sha256'] for x in author['files']}
    for n in ['candidate.md', 'original-scope.md', 'freeze-receipt.json', 'author-audit.md']:
        need(sha((root / 'inputs' / n).read_bytes()) == amap[n], 'author identity: ' + n)
    proof = read('inputs/proof-output-manifest.json')
    need(sha((root / 'inputs/proof-review.md').read_bytes()) == proof['files']['review.md'], 'proof report')
    contrib = read('inputs/contribution-output-manifest.json')
    cmap = {x['path']: x['sha256'] for x in contrib['files']}
    need(sha((root / 'inputs/contribution-review.md').read_bytes()) == cmap['review.md'], 'contribution report')
    for rec in read('source-contracts.json')['pinned_introductions']:
        data = (root / name(rec['local'])).read_bytes()
        need(sha(data) == rec['sha256'] and len(data) == rec['bytes'], 'source digest')
        need(hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == rec['git_blob'], 'Git blob')
    build = read('checks/build-receipt.json')
    need(build['source_sha256'] == sha((root / 'main.tex').read_bytes()), 'build source')
    need(build['formal_support_sha256'] == sha((root / 'formal-support.tex').read_bytes()), 'build coverage')
    pdf = root / 'output/pdf/continuum-coulomb-qma.pdf'
    need(build['pdf_sha256'] == sha(pdf.read_bytes()), 'build PDF')
    need(all(build['log_findings'][k] == 0 for k in ['overfull_boxes', 'undefined', 'rerun', 'missing_glyphs']), 'typesetting findings')
    visual = read('checks/visual-review.json')
    need(visual['status'] == 'ALL_PAGES_VIEWED_CLEAN' and visual['pdf_sha256'] == build['pdf_sha256'], 'visual status/PDF')
    page_names = [name(x['path']) for x in visual['pages']]
    need(len(set(page_names)) == len(page_names) == build['pdf_pages'] == build['rendered_pages'], 'page count')
    need(set(page_names) == {x for x in expected if x.startswith('checks/pages/') and x.endswith('.png')}, 'page membership')
    for rec in visual['pages']:
        need(rec['viewed'] is True and rec['findings'] == [], 'page not cleared')
        need(sha((root / rec['path']).read_bytes()) == rec['sha256'], 'page identity')
    formal = read('formal-dependency.json')
    need(formal['status'] == 'SEALED_COMPILED_COVERAGE_AUTHENTICATED', 'formal coverage pending')
    need(sha((root / 'inputs/formal-output-manifest.json').read_bytes()) == formal['manifest_sha256'], 'formal anchor')
    fm = read('inputs/formal-output-manifest.json')
    frows = {x['path']: x for x in fm['files']}
    for rec in formal['snapshots']:
        data = (root / name(rec['local'])).read_bytes()
        need(sha(data) == rec['sha256'] and len(data) == rec['bytes'], 'formal snapshot')
        if rec['source_path'] != 'output-manifest.json':
            need(rec['source_path'] in frows and rec['sha256'] == frows[rec['source_path']]['sha256'], 'formal manifest binding')
    cov = read('inputs/formal-coverage.json')
    need(cov['full_CM275_theorem_formalized'] is False and formal['full_theorem_formalized'] is False, 'full formal overclaim')
    need(cov['source_sha256'] == formal['source_sha256'] == sha((root / 'inputs/CM275.lean').read_bytes()), 'formal source identity')
    need('provisional' not in (root / 'formal-support.tex').read_text().lower(), 'provisional formal prose')
    public = read('public-files.json')['files']
    need(len(public) == len(set(public)), 'duplicate public file')
    for n in public:
        need(name(n) in expected and not n.startswith('private/'), 'invalid/private public file')
    print(json.dumps({'result':'INTEGRITY_OK_ONLY', 'payloads':len(expected),
                      'pages':len(page_names), 'source_blobs':3,
                      'writes':0, 'mathematics_certified':False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print('INTEGRITY_REJECT: ' + str(exc), file=sys.stderr)
        sys.exit(1)
