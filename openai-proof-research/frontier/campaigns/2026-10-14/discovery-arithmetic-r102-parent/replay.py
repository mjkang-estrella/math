#!/usr/bin/env python3
"""Authenticate a full author-proof packet and copied controls; no math gate."""
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[3]
ROOT = HERE.parent / 'fresh-arithmetic-discovery-r102'
ANCHORS = {
    'final': 'eb35ddaa80501311da50e8f65d67dc33c970530e3b00003188182b2f8ef9e34f',
    'manifest': 'e212b8f45f7fb8ae07e30ba292ea8bab83c8983c0d3311f2bd308c0a590f8a9f',
    'report': '9d5253a754956107d1920df6d67353a1169ad54b5d7f7d5bc40d7331fe35c8c2',
}
MUTABLE = 'frontier/NEW-TEN-2026-10-14.md'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def record(p):
    s = p.lstat()
    r = {'mode': stat.S_IMODE(s.st_mode), 'type': stat.S_IFMT(s.st_mode), 'links': s.st_nlink}
    if stat.S_ISLNK(s.st_mode):
        r['target'] = str(p.readlink())
    elif stat.S_ISREG(s.st_mode):
        r.update(bytes=s.st_size, sha256=sha(p))
    return r


def snap(root):
    return {str(p.relative_to(root)): record(p) for p in [root, *root.rglob('*')]}


def run(args):
    r = subprocess.run(args, text=True, capture_output=True)
    assert r.returncode == 0, (args, r.returncode, r.stderr)
    return {'exit': r.returncode, 'stdout': r.stdout, 'stderr': r.stderr}


def verify(root):
    args = [sys.executable, '-B', str(ROOT / 'verify.py'), '--root', str(root)]
    for key, value in ANCHORS.items():
        args += ['--' + key + '-sha256', value]
    return run(args)


def main():
    before = snap(ROOT)
    assert all(r['links'] == 1 for r in before.values() if r['type'] == stat.S_IFREG)
    bindings = []
    for name in ('context', 'history'):
        bindings += json.loads((ROOT / 'private' / name / 'bindings.json').read_text())
    assert len(bindings) == len({e['original'] for e in bindings}) == 14
    named = {e['original']: record(PROJECT / e['original']) for e in bindings}
    for e in bindings:
        assert sha(ROOT / e['copy']) == e['sha256']
        if e['original'] != MUTABLE:
            assert named[e['original']]['sha256'] == e['sha256'], e['original']
    result = {'kind': 'PARENT_AUTHOR_PROOF_ARTIFACT_INTAKE_NO_MATHEMATICAL_GATE',
              'anchors': ANCHORS, 'original_verification': verify(ROOT)}
    result['mutable_ledger_observation'] = {
        'path': MUTABLE, 'current_sha256': named[MUTABLE]['sha256'],
        'acquisition_sha256': next(e['sha256'] for e in bindings if e['original'] == MUTABLE),
        'adopted_as_new_mathematical_input': False,
        'limits': 'Mutable navigation copy and current file differ, as disclosed in author handoff; stable originals exclude it.'}
    with tempfile.TemporaryDirectory(prefix='copy-', dir=HERE) as td:
        mirror = Path(td) / 'project'
        copy = mirror / ROOT.relative_to(PROJECT)
        copy.parent.mkdir(parents=True)
        shutil.copytree(ROOT, copy)
        for e in bindings:
            p = mirror / e['original']
            p.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(PROJECT / e['original'], p)
        mirror_before = {rel: record(mirror / rel) for rel in named}
        result['copied_unmodified_control_runner'] = run([sys.executable, '-B', str(copy / 'controls/run_controls.py')])
        receipt = json.loads((copy / 'controls/results.json').read_text())
        assert len(receipt['cases']) == 9 and receipt['named_originals_unchanged_during_controls'] == 14
        assert all(c['expected_accept'] == c['actual_accept'] for c in receipt['cases'])
        assert [c['case'] for c in receipt['cases']] == [
            'clean', 'payload-byte', 'missing-body', 'unexpected-hidden', 'symlink',
            'mode', 'outside-report', 'wrong-final-anchor', 'forged-reseal']
        result['copied_control_cases'] = receipt['cases']
        assert all(record(mirror / rel) == r for rel, r in mirror_before.items())
    result['after_controls_original_verification'] = verify(ROOT)
    assert snap(ROOT) == before
    assert all(record(PROJECT / rel) == r for rel, r in named.items())
    result.update(all_expected=True, copied_controls=9, stable_named_originals_unchanged=13,
                  mutable_named_observations=1, named_current_files_unchanged_during_replay=14,
                  whole_actual_author_root_unchanged=True,
                  verification_summary=json.loads(result['original_verification']['stdout']),
                  scope_sha256=sha(ROOT / 'public/SCOPE.md'), proof_sha256=sha(ROOT / 'public/PROOF.md'),
                  mathematical_gate=False)
    result['limits'] = (
        'Exact complete sealed r102 root includes85 payloads/21 directories and scratch; detached envelopes '
        'and27 pinned bodies authenticate. The verifier checks retained input copies, not external originals; '
        'parent separately checks13 stable named originals and observes one mutable ledger. All14 current '
        'named files and the full actual author root remain unchanged during this replay. Supplied nine '
        'controls run unmodified in a disposable mirrored project, on newly sealed preseal-style fixtures; '
        'their copied receipt is deliberately rewritten after controls, so no unchanged final seal of that '
        'disposable runner root is claimed. Supplied cases check expected exit behavior, not independent '
        'per-fixture syscall/failure-reason audits. Production verifier does not assert single-link counts; '
        'parent current original regular files are separately checked single-link. No mathematical '
        'computation, correctness, substantiality, priority, acceptance or historical whole-workspace audit.')
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('all_expected', 'verification_summary',
        'stable_named_originals_unchanged', 'mutable_named_observations', 'copied_controls',
        'whole_actual_author_root_unchanged', 'mathematical_gate')}, sort_keys=True))


if __name__ == '__main__':
    main()
