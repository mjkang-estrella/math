#!/usr/bin/env python3
"""MIT. Read-only verifier for the T024W contribution review packet.

Usage: python3 verify.py <external manifest SHA256>

Checks the exact packet inventory against the externally anchored manifest,
the single verdict token, and the frozen r53 anchors. It then reruns the same
check on copies in a private /var/tmp directory, where every mutation must
fail with its expected reason and the unmodified copy must pass. Nothing in
the packet or the frozen r53 packet is written. Hashes do not certify
mathematics.
"""
import hashlib, json, os, shutil, stat, sys, tempfile
from pathlib import Path

FROZEN_DIR = 'fresh-arithmetic-discovery-r53'
FROZEN_ANCHORS = {
    'manifest.json': '62c538ada22690db7a5da723b46f37dd0f66d39ee31cbae1fc012c64dc6d5256',
    'scope-status.md': '066820343d15154d5ce3e737095287c1c90ba8c68c944acd3069b4ef6b84e012',
    'candidate-proof.md': '3b84f98728697371b4ca34c23b09f01d2442bc72a169395dcdd29e469883681a',
    'local-sieves.md': '499f3b67c2a4aeb51eec5b6c9fb1669dc29c99c1c48cf4923515362a9798b8e2',
    'local-coverage.md': '0da74c6445f0b3ac4cded4bf5797309c189665d1f8f79a1446c65a7f9b652bcd',
    'contribution-comparison.md': '1417af6c11bf4ea4339c558bf3464ff8192ec34ccd46fa92fe44ef8ed2031c6f',
    'reading-limits.md': '9a6e398e273f053437c0628f19865d8e9e4af1d5a991429602afb94558ce3b85',
}
VERDICTS = {'SUBSTANTIAL', 'TECHNICAL', 'DUPLICATE', 'INELIGIBLE', 'BLOCKED'}


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
    if files != m['files']:
        raise ValueError('file inventory mismatch')
    lines = [l for l in (root / 'review.md').read_text().splitlines() if l.startswith('**VERDICT: ')]
    token = lines[0][len('**VERDICT: '):].split('**')[0] if len(lines) == 1 else None
    cov = json.loads((root / 'coverage.json').read_text())
    if m.get('verdict') not in VERDICTS or token != m['verdict'] or cov.get('verdict') != m['verdict']:
        raise ValueError('verdict mismatch')
    if m.get('frozen_anchors') != FROZEN_ANCHORS or m.get('frozen_packet_dir') != FROZEN_DIR \
            or cov.get('frozen_anchors') != FROZEN_ANCHORS:
        raise ValueError('frozen anchor table mismatch')
    frozen = root.parent / FROZEN_DIR
    for name, h in FROZEN_ANCHORS.items():
        f = frozen / name
        if not f.is_file() or f.is_symlink() or sha(f.read_bytes()) != h:
            raise ValueError('frozen packet anchor mismatch: ' + name)
    return {'files': len(files), 'directories': len(dirs), 'verdict': m['verdict'],
            'frozen_anchors': len(FROZEN_ANCHORS)}


def _append(p, b=b'\n'):
    with open(p, 'ab') as f:
        f.write(b)


def _reanchor(pkt, mutate):
    mp = pkt / 'manifest.json'
    m = json.loads(mp.read_text()); mutate(m)
    mp.write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')
    return sha(mp.read_bytes())


def controls(root, expected):
    def verdict_swap(pkt):
        return _reanchor(pkt, lambda m: m.__setitem__('verdict', 'SUBSTANTIAL'))

    def anchor_table(pkt):
        def mut(m):
            m['frozen_anchors'] = dict(m['frozen_anchors'], **{'scope-status.md': '0' * 64})
        return _reanchor(pkt, mut)

    def nested(pkt):
        (pkt / 'sub').mkdir(); (pkt / 'sub' / 'manifest.json').write_text('{}')

    cases = [
        ('positive', None, None),
        ('wrong-anchor', lambda p: '0' * 64, 'external manifest anchor mismatch'),
        ('review-edit', lambda p: _append(p / 'review.md'), 'file inventory mismatch'),
        ('missing-file', lambda p: (p / 'coverage.json').unlink(), 'file inventory mismatch'),
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
        ('anchor-table-edit', anchor_table, 'frozen anchor table mismatch'),
    ]
    tmp = Path(tempfile.mkdtemp(prefix='t024w-contribution-controls-', dir='/var/tmp'))
    results = []
    try:
        for name, mutate, reason in cases:
            base = tmp / name; base.mkdir()
            pkt = base / root.name
            shutil.copytree(root, pkt, symlinks=True)
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
    script = Path(os.path.abspath(__file__))
    if '..' in Path(__file__).parts:
        raise ValueError('parent traversal in invocation')
    root = script.parent
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
