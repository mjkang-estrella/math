#!/usr/bin/env python3
# ANS263 proof review r1: read-only exact-inventory verifier. MIT.
# Byte integrity only; NOT a mathematical validation of anything.
# Usage: python3 -B verify.py --anchor <SHA256 of manifest.json supplied externally>
import argparse, hashlib, json, os, stat, subprocess, sys
from pathlib import Path, PurePosixPath

SCHEMA = 'ans263-proof-r1-inventory-v1'
# Reviewed immutable author inputs (fixed in code, not trusted from the manifest).
AUTHOR_DIR = '../fresh-analytic-discovery-r32'
AUTHOR_HASHES = {
    'manifest.json': '0e1af1b06709a0585a8724e3a15e59e228a65f4c88ee363ef88e7aa482c73cf2',
    '263-working-proof.md': 'eef51e8d50cfaf29c971e346cc4f2957f40dfe033bda3de3d2543586879c7a48',
    '263-scope.md': '03dd0d2eb2987fbc87bf130b7fe1978caa1755e7eb0286f616fc6ccfe13cf5fc',
}


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def safe_rel(s):
    p = PurePosixPath(s)
    require(isinstance(s, str) and str(p) == s and not p.is_absolute()
            and '..' not in p.parts and s not in ('', '.'), 'unsafe path: %r' % (s,))


def inventory(root):
    files, dirs = {}, []
    for base, ds, fs in os.walk(root, followlinks=False):
        for n in ds + fs:
            p = Path(base) / n
            st = p.lstat()
            rel = p.relative_to(root).as_posix()
            require(not stat.S_ISLNK(st.st_mode), 'symlink: ' + rel)
            if stat.S_ISDIR(st.st_mode):
                dirs.append(rel)
            else:
                require(stat.S_ISREG(st.st_mode), 'nonregular: ' + rel)
                require(st.st_nlink == 1, 'hardlink: ' + rel)
                if rel != 'manifest.json':
                    files[rel] = {'bytes': st.st_size, 'sha256': sha(p.read_bytes())}
    return files, sorted(dirs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--root', default=str(Path(__file__).absolute().parent))
    ap.add_argument('--skip-author', action='store_true',
                    help='do not re-hash the author packet (for relocated copies)')
    ns = ap.parse_args()
    require(len(ns.anchor) == 64 and all(c in '0123456789abcdef' for c in ns.anchor),
            'anchor must be lowercase SHA256 hex')
    root = Path(ns.root).absolute()
    for p in [root] + list(root.parents):
        require(not p.is_symlink(), 'symlink root/ancestor')
    require(root.is_dir(), 'missing root')
    mp = root / 'manifest.json'
    require(mp.is_file() and not mp.is_symlink() and mp.stat().st_nlink == 1, 'unsafe manifest')
    raw = mp.read_bytes()
    # Anchor first: nothing else is parsed before the external hash matches.
    require(sha(raw) == ns.anchor, 'external anchor mismatch')
    m = json.loads(raw)
    require(m.get('schema') == SCHEMA, 'schema')
    for s in m['files']:
        safe_rel(s)
        require(s != 'manifest.json', 'self entry')
    for s in m['directories']:
        safe_rel(s)
    files, dirs = inventory(root)
    require(files == m['files'], 'exact file inventory/hash mismatch')
    require(dirs == m['directories'], 'exact directory inventory mismatch')
    require(m.get('reviewed_author_hashes') == AUTHOR_HASHES, 'reviewed author hashes differ')
    author_checked = 0
    if not ns.skip_author:
        ad = (root / AUTHOR_DIR).resolve()
        for name, h in AUTHOR_HASHES.items():
            require(sha((ad / name).read_bytes()) == h, 'author input changed: ' + name)
            author_checked += 1
    script = root / 'checks' / 'independent_arith.py'
    out = subprocess.run([sys.executable, '-I', '-B', str(script)],
                         check=True, capture_output=True, text=True).stdout
    require(json.loads(out) == json.loads((root / 'checks' / 'independent-arith.json').read_text()),
            'arithmetic replay changed')
    print(json.dumps({
        'status': 'PASS_INTEGRITY_ONLY',
        'payload_files': len(files),
        'directories': len(dirs),
        'author_inputs_rehashed': author_checked,
        'arithmetic_replay': 'PASS_ARITHMETIC_ONLY',
        'verdict_recorded': m.get('verdict'),
        'limits': 'Byte integrity and arithmetic replay only; no proof, novelty, formal or acceptance verdict.',
    }, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:  # noqa: BLE001
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
