#!/usr/bin/env python3
"""MIT. Read-only integrity verifier for the T024W proof review r1 directory.

Usage: python3 verify.py <external SHA256 of this directory's manifest.json>

Checks the exact inventory of this directory against its externally anchored
manifest, then the frozen r53 packet (seven parent anchors and its full anchored
inventory), and independently re-authenticates all non-PDF blobs of the two
source families against sources/preprints-tree.json. It never writes anything
and certifies bytes only, not mathematics.
"""
import hashlib, json, os, stat, sys
from pathlib import Path

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
R53 = 'fresh-arithmetic-discovery-r53'
R53_ANCHORS = {
    'manifest.json': '62c538ada22690db7a5da723b46f37dd0f66d39ee31cbae1fc012c64dc6d5256',
    'scope-status.md': '066820343d15154d5ce3e737095287c1c90ba8c68c944acd3069b4ef6b84e012',
    'candidate-proof.md': '3b84f98728697371b4ca34c23b09f01d2442bc72a169395dcdd29e469883681a',
    'local-sieves.md': '499f3b67c2a4aeb51eec5b6c9fb1669dc29c99c1c48cf4923515362a9798b8e2',
    'local-coverage.md': '0da74c6445f0b3ac4cded4bf5797309c189665d1f8f79a1446c65a7f9b652bcd',
    'contribution-comparison.md': '1417af6c11bf4ea4339c558bf3464ff8192ec34ccd46fa92fe44ef8ed2031c6f',
    'reading-limits.md': '9a6e398e273f053437c0628f19865d8e9e4af1d5a991429602afb94558ce3b85',
}
FAMILIES = {
    'An-asymptotic-formula-for-the-number-of-totients-September-25-2026': 'private/source024',
    'Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026': 'private/fiber-companion',
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def read_regular(p):
    s = p.lstat()
    if not stat.S_ISREG(s.st_mode):
        raise ValueError('nonregular entry: ' + str(p))
    return p.read_bytes()


def inventory(root):
    files, dirs = {}, []

    def walk(p):
        for entry in sorted(os.scandir(p), key=lambda e: e.name):
            q = Path(entry.path)
            rel = q.relative_to(root).as_posix()
            s = q.lstat()
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel)
                walk(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1:
                    raise ValueError('hardlink: ' + rel)
                if q.name == 'manifest.json' and rel != 'manifest.json':
                    raise ValueError('nested manifest: ' + rel)
                files[rel] = {'bytes': s.st_size, 'sha256': sha(q.read_bytes())}
            else:
                raise ValueError('nonregular entry: ' + rel)
    walk(root)
    return files, sorted(dirs)


def check(anchor):
    script = Path(os.path.abspath(sys.argv[0]))
    root = script.parent
    for p in (root, *root.parents):
        if not stat.S_ISDIR(p.lstat().st_mode):
            raise ValueError('non-directory or symlink ancestor')

    files, dirs = inventory(root)
    raw = read_regular(root / 'manifest.json')
    if sha(raw) != anchor:
        raise ValueError('external manifest anchor mismatch')
    manifest = json.loads(raw)
    del files['manifest.json']
    if dirs != manifest['directories'] or files != manifest['files']:
        raise ValueError('file inventory mismatch')

    pkt = root.parent / R53
    for name, want in R53_ANCHORS.items():
        if sha(read_regular(pkt / name)) != want:
            raise ValueError('frozen r53 anchor mismatch: ' + name)

    repo = root.parents[3]
    treeb = read_regular(repo / 'sources' / 'preprints-tree.json')
    tree = json.loads(treeb)
    if sha(treeb) != TREE_SHA or tree['truncated'] is not False or len(tree['tree']) != 13223:
        raise ValueError('canonical tree mismatch')
    if json.loads(read_regular(repo / 'sources' / 'upstream.json'))['commit'] != PIN:
        raise ValueError('pin mismatch')
    blobs = 0
    for e in tree['tree']:
        parts = e['path'].split('/')
        if len(parts) < 3 or parts[1] not in FAMILIES or e['type'] != 'blob':
            continue
        if e['path'].lower().endswith('.pdf'):
            continue
        local = pkt / FAMILIES[parts[1]] / '/'.join(parts[2:])
        b = read_regular(local)
        if hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() != e['sha']:
            raise ValueError('source blob identity mismatch: ' + e['path'])
        blobs += 1
    if blobs != 22:
        raise ValueError('source blob count mismatch')

    pfiles, pdirs = inventory(pkt)
    pman = json.loads(read_regular(pkt / 'manifest.json'))
    del pfiles['manifest.json']
    if pdirs != pman['directories'] or pfiles != pman['files']:
        raise ValueError('r53 inventory mismatch')

    print(json.dumps({'status': 'PASS_EXACT_INVENTORY', 'review_files': len(files),
                      'r53_anchors': len(R53_ANCHORS), 'r53_files': len(pfiles),
                      'r53_directories': len(pdirs), 'source_blobs': blobs,
                      'note': 'bytes only; not a mathematical certificate'}))


if __name__ == '__main__':
    try:
        if len(sys.argv) != 2 or len(sys.argv[1]) != 64 or any(c not in '0123456789abcdef' for c in sys.argv[1]):
            raise ValueError('external SHA256 argument required')
        check(sys.argv[1])
    except Exception as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        sys.exit(1)
