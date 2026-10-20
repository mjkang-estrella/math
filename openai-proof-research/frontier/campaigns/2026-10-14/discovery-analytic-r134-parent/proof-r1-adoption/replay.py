#!/usr/bin/env python3
"""Parent artifact adoption only; analytic correctness comes from the review."""
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
REVIEW = BASE / 'k369r134-proof-r1'
AUTHOR = BASE / 'fresh-analytic-discovery-r134'
ANCHORS = {
    'FINAL.json': '09a37050f69e5d477b23f70cf1e78572d396f67e5711f112c7a811d4f9c792d4',
    'MANIFEST.json': '8710f2d532600a72322766b360fefc90f7c8572f2a867af5196a7693b62cbb6f',
    'REPORT.md': '7f83342695aeff17f8cb8705c8550f9344a2058b17c54392b167c4ab65380d50',
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def snapshot(root, skip=()):
    result = {}
    for base, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(n for n in dirs if n not in skip)
        for name in sorted(dirs + files):
            p = Path(base) / name
            s = p.lstat()
            assert stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode), p
            row = {'kind': 'directory' if p.is_dir() else 'file',
                   'mode': stat.S_IMODE(s.st_mode)}
            if p.is_file():
                row.update(bytes=s.st_size, sha256=sha(p), nlink=s.st_nlink)
            result[p.relative_to(root).as_posix()] = row
    return result


def main():
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    protected = [PROJECT / 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json',
                 PROJECT / 'frontier/iterations/i31-nonconical-no-mcm.md']
    protected_before = {str(p.relative_to(PROJECT)): sha(p) for p in protected}
    assert protected_before == {
        'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json': '6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9',
        'frontier/iterations/i31-nonconical-no-mcm.md': 'd606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a',
    }
    assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=PROJECT)
    old_tasks = json.loads((BASE / 'tasks.json').read_text())
    dump('integration-baseline.json', {
        'observed_utc': started,
        'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
        'initial_index_empty': True, 'protected_unrelated_sha256': protected_before,
        'task_count': len(old_tasks['tasks']), 'proof_task_index': 461,
        'accepted': old_tasks['newAccepted'], 'remaining': old_tasks['remaining'],
        'tasks_sha256': sha(BASE / 'tasks.json'),
    })
    before = {'review': snapshot(REVIEW), 'author': snapshot(AUTHOR),
              'older_parent': snapshot(OUT.parent, skip=('proof-r1-adoption',))}
    dump('observed-roots.json', {'observed_utc': started, 'roots': before,
         'limits': 'Current parent observation after semantic reads, before copied execution. File/directory identity, modes and file links over this interval only; not historical whole-workspace preservation.'})
    for name, value in ANCHORS.items():
        assert sha(REVIEW / name) == value
    final = json.loads((REVIEW / 'FINAL.json').read_text())
    assert sha(REVIEW / 'verify.py') == final['verifier_sha256']
    assert final['verdict'] == 'PASS_FULL_K369R134'
    assert final['scope_unchanged'] and not final['required_repairs']
    assert not final['unresolved_correctness_obligations']
    assert sha(AUTHOR / 'packet/public/FROZEN-SCOPE.md') == final['frozen_scope_sha256']
    assert sha(AUTHOR / 'packet/public/author-proof.md') == final['author_proof_sha256']
    author_files = {n: {'bytes': x['bytes'], 'sha256': x['sha256']}
                    for n, x in before['author'].items() if x['kind'] == 'file'}
    assert author_files == json.loads((REVIEW / 'packet/private/author-before.json').read_text())
    copied_author = REVIEW / 'packet/private/author-copy'
    tree_bytes = (PROJECT / 'sources/preprints-tree.json').read_bytes()
    assert hashlib.sha256(tree_bytes).hexdigest() == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_bytes)
    entries = tree['tree'] if isinstance(tree, dict) else tree
    assert len(entries) == 13223
    paths = {x['path']: x for x in entries}
    source_checks = []
    for row in json.loads((copied_author / 'packet/private/source-acquisition.json').read_text()):
        p = copied_author / 'packet/private/source' / Path(row['local']).name
        b = p.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert len(b) == row['size'] == paths[row['path']]['size']
        assert blob == row['sha'] == paths[row['path']]['sha']
        assert sha(p) == row['sha256']
        source_checks.append({'path': row['path'], 'bytes': len(b), 'sha256': sha(p), 'gitblob': blob})
    bindings = []
    for row in json.loads((copied_author / 'packet/private/late-bindings.json').read_text()):
        assert sha(copied_author / row['copy']) == row['sha256']
        current = sha(Path(row['original_path']))
        if not row['mutable_observation']:
            assert current == row['sha256']
        bindings.append({'path': row['original_path'], 'capture_sha256': row['sha256'],
                         'current_sha256': current, 'currently_matches': current == row['sha256'],
                         'mutable_observation': row['mutable_observation']})
    args = ['--final-sha256', ANCHORS['FINAL.json'], '--manifest-sha256',
            ANCHORS['MANIFEST.json'], '--report-sha256', ANCHORS['REPORT.md']]
    with tempfile.TemporaryDirectory(prefix='copied-review-', dir=OUT) as tmp:
        copy = Path(tmp) / 'review'
        shutil.copytree(REVIEW, copy)
        command = [sys.executable, '-B', str(copy / 'packet/public/artifact_controls.py'),
                   '--root', str(copy), *args, '--receipt', str(copy / 'parent-controls.json')]
        run = subprocess.run(command, capture_output=True, text=True, timeout=90)
        assert run.returncode == 0, (run.stdout, run.stderr)
        controls = json.loads((copy / 'parent-controls.json').read_text())
        assert len(controls['cases']) == 6
        assert all(x['expected_outcome'] for x in controls['cases'])
        dump('copied-controls.json', controls)
        output = {'returncode': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr}
    after = {'review': snapshot(REVIEW), 'author': snapshot(AUTHOR),
             'older_parent': snapshot(OUT.parent, skip=('proof-r1-adoption',))}
    assert before == after
    assert all(sha(PROJECT / p) == h for p, h in protected_before.items())
    dump('replay.json', {
        'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'external_handoff_anchors': ANCHORS, 'verifier_identity': final['verifier_sha256'],
        'status': 'PASS_ARTIFACT_SUPPORT_ONLY', 'review_payload_files': final['packet_files'],
        'review_root_files': sum(x['kind'] == 'file' for x in before['review'].values()),
        'author_root_files': len(author_files), 'author_matches_review_observation': True,
        'pinned_sources': source_checks, 'late_input_comparisons': bindings,
        'copied_controls': output, 'control_cases': 6, 'negative_cases': 4,
        'observed_roots_unchanged': True, 'protected_unrelated_unchanged': True,
        'limits': 'Six review-artifact cases only, four negative. Author 177 exact support checks and nine author-artifact cases were reproduced at prior parent intake, not rerun here. Review verifier checks exact regular files, not empty dirs/modes/hardlinks/current originals/Git blobs; separate parent snapshots and source/input comparisons cover only named present observations. No finite check establishes analytic correctness. Private copied bodies remain local; current mutable ledger mismatch is expected. No contribution, acceptance, full formalization, manuscript or release gate.'
    })
    print(json.dumps({'artifact_support': 'PASS', 'review_files': final['packet_files'],
                      'source_blobs': len(source_checks), 'control_cases': 6,
                      'negative_cases': 4, 'roots_unchanged': True}))


if __name__ == '__main__':
    main()
