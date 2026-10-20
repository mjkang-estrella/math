#!/usr/bin/env python3
"""Parent contribution intake: byte observations, not a mathematical gate."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

OUT = Path(__file__).resolve().parent
BASE = OUT.parent.parent
PROJECT = BASE.parents[2]
ROOT = BASE / 't373e135-contribution-r1'
AUTHOR = BASE / 'fresh-analytic-discovery-r135'
ANCHORS = {
    'FINAL.md': 'abec08760e057f6d9c396937e91275e651c93b219f40511fd7e90030d60e4730',
    'packet/MANIFEST.json': '5c267d0121640b98c2533eb0b9d7bfd13c684d1c0cd28076ed49e16bf2c71b1f',
    'REPORT.md': 'febcd22b08a2319c0484f8feec6bff2535a73272c8fdd73d35d93a6b7e510442',
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def snap(root):
    rows = {}
    for cur, dirs, files in os.walk(root, followlinks=False):
        for name in sorted(dirs + files):
            p = Path(cur) / name
            s = p.lstat()
            row = {'mode': stat.S_IMODE(s.st_mode)}
            if p.is_symlink():
                row.update(kind='symlink', target=os.readlink(p))
            elif stat.S_ISDIR(s.st_mode):
                row.update(kind='directory')
            elif stat.S_ISREG(s.st_mode):
                row.update(kind='file', bytes=s.st_size, sha256=sha(p), nlink=s.st_nlink)
            else:
                raise AssertionError(p)
            rows[p.relative_to(root).as_posix()] = row
    return rows


def main():
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    before, author_before = snap(ROOT), snap(AUTHOR)
    dump('observed-roots.json', {'observed_utc': now, 'review_root': before,
                                'author_root': author_before,
                                'limits': 'Current roots after prose/code reading; no historical whole-parent claim.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    assert sha(ROOT / 'packet/public/verify_packet.py') == '4c46b377e6313ae93cc15f6b082590f34f64233d28eb9a574df6d9a2bb20f82e'
    assert sha(ROOT / 'packet/public/FROZEN-SCOPE.md') == 'cc80f307514d0fe7ab47079b6cda7d47abb7ce4c80aa616d0ebc02cc1b96e939'
    assert (ROOT / 'packet/public/FROZEN-SCOPE.md').read_bytes() == (AUTHOR / 'packet/public/FROZEN-SCOPE.md').read_bytes()
    old = json.loads((ROOT / 'packet/private/current-originals-before-copy.json').read_text())
    assert len(old['author_root']) == 89
    assert {p: e['sha256'] for p, e in author_before.items() if e['kind'] == 'file'} == old['author_root']
    selected = []
    for p, h in old['selected_originals'].items():
        current = sha(PROJECT / p)
        mutable = p == 'frontier/NEW-TEN-2026-10-14.md'
        if not mutable:
            assert current == h, p
        selected.append({'path': p, 'review_snapshot_sha256': h,
                         'current_sha256': current, 'mutable_observation': mutable,
                         'unchanged_since_review_snapshot': current == h})
    selected_before = {e['path']: e['current_sha256'] for e in selected}
    tree_path = PROJECT / 'sources/preprints-tree.json'
    assert sha(tree_path) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_path.read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    index = {e['path']: e for e in tree['tree']}
    incoming = ROOT / 'packet/private/incoming-copy/fresh-analytic-discovery-r135'
    sources = json.loads((ROOT / 'packet/private/canonical-pinned-source-check.json').read_text())['blobs']
    for e in sources:
        p = incoming / 'packet/private/upstream' / e['canonical_path']
        b = p.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert len(b) == e['size'] == index[e['canonical_path']]['size']
        assert blob == e['git_blob'] == index[e['canonical_path']]['sha'] and sha(p) == e['sha256']
    primary_rows = []
    primary = incoming / 'packet/private/primary'
    for n in ['acquisitions.json', 'late-acquisitions.json', 'parametrix-acquisition.json', 'dgw-acquisition.json']:
        rows = json.loads((primary / n).read_text())
        if isinstance(rows, dict):
            name = {'parametrix-acquisition.json': 'parametrix', 'dgw-acquisition.json': 'djellout-guillin-wu-v1'}[n]
            rows = [dict(rows, name=name)]
        for e in rows:
            p = primary / (e['name'] + '.pdf')
            assert sha(p) == e['sha256'] and p.stat().st_size == e['size']
            primary_rows.append(e)
    primary = ROOT / 'packet/private/primary'
    for e in json.loads((primary / 'acquisitions.json').read_text()):
        p = primary / (e['name'] + '.pdf')
        assert sha(p) == e['sha256'] and p.stat().st_size == e['bytes']
        primary_rows.append(e)
    controls = []
    with tempfile.TemporaryDirectory(prefix='contribution-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'review'
        shutil.copytree(ROOT, copy)
        args = [sys.executable, '-B', str(copy / 'packet/public/verify_packet.py'), str(copy),
                '--final-sha', ANCHORS['FINAL.md'], '--manifest-sha', ANCHORS['packet/MANIFEST.json'],
                '--report-sha', ANCHORS['REPORT.md']]

        def check(name, expected):
            state = snap(copy)
            proc = subprocess.run(args, capture_output=True, text=True, timeout=30)
            assert (proc.returncode == 0) == expected, (name, proc.stdout, proc.stderr)
            assert snap(copy) == state
            controls.append({'case': name, 'expected_pass': expected, 'returncode': proc.returncode,
                             'fixture_unchanged': True, 'stdout': proc.stdout.strip(), 'stderr': proc.stderr.strip()})

        check('baseline', True)
        p = copy / 'packet/public/review.md'
        b = p.read_bytes()
        p.write_bytes(b + b'\nCONTROL\n')
        check('modified_review', False)
        p.unlink()
        check('missing_review', False)
        p.write_bytes(b)
        p = copy / 'packet/extra-control'
        p.write_text('control')
        check('extra_payload', False)
        p.unlink()
        p.symlink_to('public/review.md')
        check('symlink_payload', False)
        p.unlink()
        for n in ['FINAL.md', 'REPORT.md', 'packet/MANIFEST.json']:
            p = copy / n
            b = p.read_bytes()
            p.write_bytes(b + b'\n')
            check('altered_' + n, False)
            p.write_bytes(b)
        check('restored', True)
        assert snap(copy) == before
    assert snap(ROOT) == before and snap(AUTHOR) == author_before
    assert all(sha(PROJECT / p) == h for p, h in selected_before.items())
    dump('copied-controls.json', {'cases': controls, 'positive_cases': 2, 'negative_cases': 7,
                                 'original_review_and_author_roots_unchanged': True})
    manifest = json.loads((ROOT / 'packet/MANIFEST.json').read_text())
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                         'external_handoff_anchors': ANCHORS, 'payload_files': len(manifest['files']),
                         'review_root_files': sum(e['kind'] == 'file' for e in before.values()),
                         'author_files': 89, 'author_root_matches_review_snapshot': True,
                         'pinned_source_blobs': len(sources), 'primary_pdf_receipts': primary_rows,
                         'selected_project_inputs': selected, 'artifact_cases': 9, 'negative_cases': 7,
                         'review_and_author_roots_unchanged': True, 'selected_inputs_unchanged_during_replay': True,
                         'limits': 'Byte/metadata observations only. No new correctness or contribution gate; no historical whole-parent preservation, OS isolation, whole-literature reading or priority claim.'})
    print(json.dumps({'payload_files': len(manifest['files']), 'author_files': 89,
                      'pinned_source_blobs': len(sources), 'primary_pdfs': len(primary_rows),
                      'artifact_cases': 9, 'negative_cases': 7, 'roots_unchanged': True}))


if __name__ == '__main__':
    main()
