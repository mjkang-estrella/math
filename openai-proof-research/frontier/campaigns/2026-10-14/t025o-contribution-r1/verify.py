#!/usr/bin/env python3
"""MIT. Read-only verifier for the T025O54 contribution review packet.

Usage: python3 -B verify.py <external manifest SHA256>

Adapted from t024w-contribution-r1/verify.py (SHA256 19ad2b27...ba8be1, commit 3f997996).
Checks the exact packet inventory against the externally anchored manifest, the single
verdict token in review.md/checks.json/manifest.json, the frozen r54 anchors, and that a
fresh run of diagnostics.py reproduces the recorded finite diagnostics. It then reruns the
check on disposable copies under /var/tmp, where each mutation must fail with its expected
reason and the unmodified copy must pass. Nothing in this packet or the frozen r54 packet is
written. Hashes and finite diagnostics do not certify mathematics.
"""
import hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path

FROZEN_DIR = 'fresh-arithmetic-discovery-r54'
FROZEN_ANCHORS = {
    'manifest.json': 'e32e49cd36807d4c18291bb60d45f6431e48fb0c61566bfcc6ca4f30a4c3ddd3',
    'scope-status.md': 'f6da553993dc03592a52711922035d412ca21b6840194fb4b3440e8e7415e0b6',
    'candidate-proof.md': '74217f39dd39087e9881c78048bf5ec1822218f4da997089feb36142265a9ef7',
    'constrained-descent.md': '4cdab2ae581fb42e4db335c41db32e797285c91fcf7669535e1900eded11a636',
    'contribution-comparison.md': '2282e8107869ac40d9393a328ab3f2ff64e85cb89f209ae02b65e80ca3adbac7',
    'reading-limits.md': 'a78dca74d4d00b5bd8c5bf3e803f90ec789e28ed751331a45a248568685cba43',
    'alternative-route.md': '829fe320bb5e293ee22325373b667fbcec9489f637491b07c31491c9e873e932',
}
VERDICTS = {'SUBSTANTIAL', 'TECHNICAL', 'DUPLICATE', 'INELIGIBLE', 'BLOCKED'}
EXPECTED_FILES = {'review.md', 'reading-limits.md', 'checks.json', 'diagnostics.py', 'verify.py'}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def check(root, expected):
    root = Path(root)
    for p in (root, *root.parents):
        if not stat.S_ISDIR(p.lstat().st_mode):
            raise ValueError('non-directory or symlink ancestor')
    files, dirs = {}, []

    def walk(p):
        for entry in sorted(os.scandir(p), key=lambda e: e.name):
            q = Path(entry.path); rel = q.relative_to(root).as_posix(); s = q.lstat()
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel); walk(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1:
                    raise ValueError('hardlink: ' + rel)
                if q.name == 'manifest.json' and rel != 'manifest.json':
                    raise ValueError('nested manifest')
                files[rel] = {'bytes': s.st_size, 'sha256': sha(q.read_bytes())}
            else:
                raise ValueError('nonregular entry: ' + rel)
    walk(root)
    raw = (root / 'manifest.json').read_bytes()
    if sha(raw) != expected:
        raise ValueError('external manifest anchor mismatch')
    m = json.loads(raw)
    if sorted(dirs) != m['directories']:
        raise ValueError('directory inventory mismatch')
    del files['manifest.json']
    if files != m['files'] or set(files) != EXPECTED_FILES:
        raise ValueError('file inventory mismatch')
    lines = [l for l in (root / 'review.md').read_text().splitlines() if l.startswith('**VERDICT: ')]
    token = lines[0][len('**VERDICT: '):].split('**')[0] if len(lines) == 1 else None
    chk = json.loads((root / 'checks.json').read_text())
    if m.get('verdict') not in VERDICTS or token != m['verdict'] or chk.get('verdict') != m['verdict']:
        raise ValueError('verdict mismatch')
    if m.get('frozen_anchors') != FROZEN_ANCHORS or m.get('frozen_packet_dir') != FROZEN_DIR \
            or chk.get('frozen_anchors') != FROZEN_ANCHORS:
        raise ValueError('frozen anchor table mismatch')
    frozen = root.parent / FROZEN_DIR
    for name, h in FROZEN_ANCHORS.items():
        f = frozen / name
        if not f.is_file() or f.is_symlink() or sha(f.read_bytes()) != h:
            raise ValueError('frozen packet anchor mismatch: ' + name)
    run = subprocess.run([sys.executable, '-B', str(root / 'diagnostics.py')], capture_output=True,
                         text=True, timeout=600)
    if run.returncode != 0 or json.loads(run.stdout) != chk.get('diagnostics'):
        raise ValueError('diagnostic record mismatch')
    d = chk['diagnostics']
    if not (d['templates'] is True and d['residue_equivalence']['mismatches'] == 0
            and d['scaling_identity_mismatches'] == 0):
        raise ValueError('diagnostic failure recorded')
    return {'files': len(files), 'directories': len(dirs), 'verdict': m['verdict'],
            'frozen_anchors': len(FROZEN_ANCHORS)}


def _append(p, b=b'\n'):
    with open(p, 'ab') as f:
        f.write(b)


def _write_manifest(pkt, m):
    mp = pkt / 'manifest.json'
    mp.write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')
    return sha(mp.read_bytes())


def _reanchor(pkt, mutate):
    m = json.loads((pkt / 'manifest.json').read_text()); mutate(m)
    return _write_manifest(pkt, m)


def _edit_tracked(pkt, name, edit):
    p = pkt / name
    p.write_text(edit(p.read_text()))
    m = json.loads((pkt / 'manifest.json').read_text())
    b = p.read_bytes(); m['files'][name] = {'bytes': len(b), 'sha256': sha(b)}
    return _write_manifest(pkt, m)


def controls(root, expected):
    def verdict_swap(pkt):
        return _reanchor(pkt, lambda m: m.__setitem__('verdict', 'SUBSTANTIAL'))

    def review_token_swap(pkt):
        return _edit_tracked(pkt, 'review.md',
                             lambda s: s.replace('**VERDICT: TECHNICAL**', '**VERDICT: SUBSTANTIAL**', 1))

    def anchor_table(pkt):
        def mut(m):
            m['frozen_anchors'] = dict(m['frozen_anchors'], **{'scope-status.md': '0' * 64})
        return _reanchor(pkt, mut)

    def diag_record(pkt):
        def ed(s):
            c = json.loads(s); c['diagnostics']['residue_equivalence']['cases'] = 19999
            return json.dumps(c, indent=2, sort_keys=True) + '\n'
        return _edit_tracked(pkt, 'checks.json', ed)

    def diag_code(pkt):
        return _edit_tracked(pkt, 'diagnostics.py', lambda s: s.replace('[7, 9, 33, 693]', '[7, 9, 33, 691]', 1))

    def nested(pkt):
        (pkt / 'sub').mkdir(); (pkt / 'sub' / 'manifest.json').write_text('{}')

    cases = [
        ('positive', None, None),
        ('wrong-anchor', lambda p: '0' * 64, 'external manifest anchor mismatch'),
        ('review-edit', lambda p: _append(p / 'review.md'), 'file inventory mismatch'),
        ('missing-file', lambda p: (p / 'checks.json').unlink(), 'file inventory mismatch'),
        ('extra-file', lambda p: (p / 'extra.txt').write_text('x'), 'file inventory mismatch'),
        ('extra-dir', lambda p: (p / 'extra').mkdir(), 'directory inventory mismatch'),
        ('symlink', lambda p: os.symlink('review.md', p / 'link.md'), 'nonregular entry'),
        ('hardlink', lambda p: os.link(p / 'review.md', p / 'review-link.md'), 'hardlink'),
        ('nested-manifest', nested, 'nested manifest'),
        ('frozen-edit', lambda p: _append(p.parent / FROZEN_DIR / 'candidate-proof.md'),
         'frozen packet anchor mismatch'),
        ('frozen-missing', lambda p: (p.parent / FROZEN_DIR / 'scope-status.md').unlink(),
         'frozen packet anchor mismatch'),
        ('verdict-swap', verdict_swap, 'verdict mismatch'),
        ('review-token-swap', review_token_swap, 'verdict mismatch'),
        ('anchor-table-edit', anchor_table, 'frozen anchor table mismatch'),
        ('diagnostic-record-edit', diag_record, 'diagnostic record mismatch'),
        ('diagnostic-code-edit', diag_code, 'diagnostic record mismatch'),
    ]
    tmp = Path(tempfile.mkdtemp(prefix='t025o-contribution-controls-', dir='/var/tmp'))
    results = []
    try:
        for name, mutate, reason in cases:
            base = tmp / name; base.mkdir()
            pkt = base / root.name
            shutil.copytree(root, pkt, symlinks=True, ignore=shutil.ignore_patterns('__pycache__'))
            (base / FROZEN_DIR).mkdir()
            for f in FROZEN_ANCHORS:
                shutil.copyfile(root.parent / FROZEN_DIR / f, base / FROZEN_DIR / f)
            anchor = expected
            if mutate is not None:
                out = mutate(pkt)
                if isinstance(out, str):
                    anchor = out
            try:
                check(pkt, anchor)
                got = None
            except ValueError as e:
                got = str(e)
            ok = (got is None) if reason is None else (got is not None and got.startswith(reason))
            results.append({'case': name, 'expected': reason, 'got': got, 'ok': ok})
            if not ok:
                raise ValueError('control failed: %s expected %r got %r' % (name, reason, got))
    finally:
        shutil.rmtree(tmp)
    return results


def main():
    if len(sys.argv) != 2 or len(sys.argv[1]) != 64 or any(c not in '0123456789abcdef' for c in sys.argv[1]):
        raise ValueError('external SHA256 argument required')
    if '..' in Path(sys.argv[0]).parts:
        raise ValueError('parent traversal in invocation')
    root = Path(os.path.abspath(__file__)).parent
    summary = check(root, sys.argv[1])
    res = controls(root, sys.argv[1])
    summary.update({'status': 'PASS_EXACT_REVIEW_PACKET', 'controls': len(res),
                    'control_reasons': {r['case']: r['expected'] for r in res}})
    print(json.dumps(summary, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
