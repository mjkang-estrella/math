#!/usr/bin/env python3
"""Parent artifact evidence only; contribution judgment is a separate decision."""
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
REVIEW = BASE / 'k369r134-contribution-r1'
AUTHOR = BASE / 'fresh-analytic-discovery-r134'
PROOF = BASE / 'k369r134-proof-r1'
ANCHORS = {
    'FINAL.json': '185af6996d2b4a621ebe24bb5466959bc6029ae9d2c0123ae23bdd1bb49656c1',
    'MANIFEST.json': '3288db6845a80c69e1a3b010efe171545c393a893c6805505d601c212bfde330',
    'REPORT.md': 'b5674138e606441d17c323fcea605891cc5771eb425fda45b36f62ebf0787261',
    'verify.py': 'aaeea311d5192e229da005d85a84ae179ba90107f34fd1901c078b109e717fc1',
    'INTEGRITY-CONTROLS.json': '096b6801a9a3a304758b33250557521a6b178523d5d38d18895d5bd14d236612',
    'ORIGINAL-PRESERVATION.json': '5877bd6bda2f194bbec8a9b65142f35d7cb181f452e0245f7da6a603aff41263',
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def snapshot(root, skip=()):
    result = {}
    for base, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(n for n in dirs if n not in skip)
        for n in sorted(dirs + files):
            p = Path(base) / n
            s = p.lstat()
            assert stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode), p
            row = {'kind': 'directory' if p.is_dir() else 'file', 'mode': stat.S_IMODE(s.st_mode)}
            if p.is_file():
                row.update(bytes=s.st_size, sha256=sha(p), nlink=s.st_nlink)
            result[p.relative_to(root).as_posix()] = row
    return result


def main():
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    protected = {
        'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json': '6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9',
        'frontier/iterations/i31-nonconical-no-mcm.md': 'd606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a',
    }
    for n, h in protected.items():
        assert sha(PROJECT / n) == h
    assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=PROJECT)
    tasks = json.loads((BASE / 'tasks.json').read_text())
    dump('integration-baseline.json', {
        'observed_utc': now,
        'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
        'initial_index_empty': True, 'protected_unrelated_sha256': protected,
        'task_count': len(tasks['tasks']), 'contribution_task_index': 462,
        'tasks_sha256': sha(BASE / 'tasks.json'), 'accepted': tasks['newAccepted'],
        'remaining': tasks['remaining'],
    })
    before = {'review': snapshot(REVIEW), 'author': snapshot(AUTHOR),
              'proof': snapshot(PROOF), 'older_parent': snapshot(OUT.parent, skip=('contribution-r1-adoption',))}
    dump('observed-roots.json', {'observed_utc': now, 'roots': before,
         'limits': 'Present observation after semantic reads and before copied execution; no historical whole-workspace preservation.'})
    for n, h in ANCHORS.items():
        assert sha(REVIEW / n) == h, n
    final = json.loads((REVIEW / 'FINAL.json').read_text())
    assert final['verifier_sha256'] == ANCHORS['verify.py']
    assert final['verdict'] == 'TECHNICAL' and final['conditional_on_correctness']
    assert final['scope'] == 'ENTIRE_UNCHANGED_FROZEN_STATEMENT'
    assert sha(REVIEW / final['review']) == final['review_sha256']
    assert sha(REVIEW / 'packet/public/check_artifact_copies.py') == final['artifact_controls_sha256']
    assert sha(AUTHOR / 'packet/public/FROZEN-SCOPE.md') == final['frozen_scope_sha256']
    assert sha(AUTHOR / 'packet/public/author-proof.md') == final['submitted_proof_sha256']
    auth = json.loads((REVIEW / 'packet/private/authentication.json').read_text())
    assert {n: x['sha256'] for n, x in before['author'].items() if x['kind'] == 'file'} == auth['author_root_before']
    tree = json.loads((PROJECT / 'sources/preprints-tree.json').read_text())
    assert sha(PROJECT / 'sources/preprints-tree.json') == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    entries = tree['tree'] if isinstance(tree, dict) else tree
    assert len(entries) == 13223
    bypath = {x['path']: x for x in entries}
    sources = []
    for row in json.loads((AUTHOR / 'packet/private/source-acquisition.json').read_text()):
        p = AUTHOR / 'packet/private/source' / Path(row['local']).name
        b = p.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert len(b) == row['size'] == bypath[row['path']]['size']
        assert blob == row['sha'] == bypath[row['path']]['sha']
        assert sha(p) == row['sha256']
        sources.append({'path': row['path'], 'bytes': len(b), 'sha256': sha(p), 'gitblob': blob})
    bindings = []
    for row in json.loads((REVIEW / 'packet/private/late-read-bindings.json').read_text()):
        if row['captured'] is not None:
            assert sha(REVIEW / row['captured']) == row['sha256']
        current = sha(Path(row['original']))
        if not row['mutable_observation']:
            assert current == row['sha256']
        bindings.append({'original': row['original'], 'capture': row['captured'],
                         'capture_sha256': row['sha256'], 'current_sha256': current,
                         'currently_matches': current == row['sha256'],
                         'mutable_observation': row['mutable_observation']})
    manifest = json.loads((REVIEW / 'MANIFEST.json').read_text())['files']
    primary = [x for x in manifest if x['path'].endswith('.pdf')]
    args = ['--final-sha256', ANCHORS['FINAL.json'], '--manifest-sha256',
            ANCHORS['MANIFEST.json'], '--report-sha256', ANCHORS['REPORT.md']]
    with tempfile.TemporaryDirectory(prefix='copied-contribution-', dir=OUT) as tmp:
        copied = Path(tmp) / 'review'
        shutil.copytree(REVIEW, copied)
        run = subprocess.run([sys.executable, '-B', str(copied / 'packet/public/check_artifact_copies.py'),
                              '--root', str(copied), *args], capture_output=True, text=True, timeout=90)
        assert run.returncode == 0, (run.stdout, run.stderr)
        receipt = json.loads((copied / 'INTEGRITY-CONTROLS.json').read_text())
        assert len(receipt['checks']) == 9 and all(x['control_pass'] for x in receipt['checks'])
        dump('copied-controls.json', receipt)
        execution = {'returncode': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr}
    after = {'review': snapshot(REVIEW), 'author': snapshot(AUTHOR),
             'proof': snapshot(PROOF), 'older_parent': snapshot(OUT.parent, skip=('contribution-r1-adoption',))}
    assert before == after
    for n, h in protected.items():
        assert sha(PROJECT / n) == h
    dump('replay.json', {
        'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status': 'PASS_ARTIFACT_SUPPORT_ONLY', 'external_handoff_anchors': ANCHORS,
        'packet_files': final['packet_files'],
        'review_root_files': sum(x['kind'] == 'file' for x in before['review'].values()),
        'actual_author_files': len(auth['author_root_before']),
        'pinned_source_blobs': sources, 'primary_pdf_records': primary,
        'late_input_comparisons': bindings, 'execution': execution,
        'copied_control_cases': 9, 'negative_cases': 6,
        'all_observed_roots_unchanged': True, 'protected_unrelated_unchanged': True,
        'limits': 'Three positive and six negative review-artifact cases. Author-artifact cases are separately historical and not rerun here. Child verifier omits empty dirs/modes/hardlinks/current originals/Git blobs; parent snapshots and named comparisons are separate current observations. Primary PDF/text byte binding is not semantic reading or fresh extraction. No finite evidence establishes contribution or correctness. Protected bodies remain local. No complete priority/exclusion/historical whole-parent or OS enforcement claim.'
    })
    print(json.dumps({'artifact_support': 'PASS', 'packet_files': final['packet_files'],
                      'review_root_files': sum(x['kind'] == 'file' for x in before['review'].values()),
                      'sources': len(sources), 'bindings': len(bindings),
                      'primary_pdfs': len(primary), 'cases': 9, 'negative': 6,
                      'roots_unchanged': True}))


if __name__ == '__main__':
    main()
