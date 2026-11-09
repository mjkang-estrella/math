"""Read-only integrity verifier for lane claude-mathdb-curvature-prior-review-r618.

Checks manifest.json: every listed payload exists with exact size and sha256, no listed path
escapes the lane or is a symlink, and no unlisted file exists except manifest.json and
final-receipt.json.  Exit 0 on PASS, 1 on any mismatch.  Writes nothing; executes no
mathematics.  Integrity PASS is not a mathematical or novelty PASS.
Usage: python3 -I -B verify.py [LANE_DIR]
"""
import hashlib, json, os, sys

EXCLUDED = ('manifest.json', 'final-receipt.json')


def load_tree(root):
    files, links = {}, []
    for d, ds, fs in os.walk(root):
        ds.sort()
        for f in sorted(fs):
            p = os.path.join(d, f); rel = os.path.relpath(p, root)
            if os.path.islink(p):
                links.append(rel); continue
            with open(p, 'rb') as h:
                files[rel] = h.read()
    return files, links


def verify_tree(files, manifest, links=()):
    errs = []
    if links:
        errs.append('symlinks present: %s' % sorted(links))
    entries = manifest.get('files')
    if not isinstance(entries, list) or not entries:
        return ['manifest has no files list']
    seen = set()
    for e in entries:
        p = e.get('path', '')
        if (not p or p.startswith('/') or '..' in p.split('/') or p in EXCLUDED
                or p in seen):
            errs.append('bad or duplicate path: %r' % p); continue
        seen.add(p)
        if p not in files:
            errs.append('missing: %s' % p); continue
        b = files[p]
        if len(b) != e.get('size'):
            errs.append('size mismatch: %s' % p)
        if hashlib.sha256(b).hexdigest() != e.get('sha256'):
            errs.append('sha256 mismatch: %s' % p)
    extra = sorted(set(files) - seen - set(EXCLUDED))
    if extra:
        errs.append('unlisted files: %s' % extra)
    if sorted(manifest.get('excluded_exact_paths', [])) != sorted(EXCLUDED):
        errs.append('excluded_exact_paths altered')
    return errs


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    files, links = load_tree(root)
    if 'manifest.json' not in files:
        print(json.dumps({'status': 'FAIL', 'errors': ['manifest.json missing']})); return 1
    manifest = json.loads(files['manifest.json'])
    errs = verify_tree(files, manifest, links)
    print(json.dumps({'status': 'FAIL' if errs else 'PASS', 'checked': len(manifest['files']),
                      'manifest_sha256': hashlib.sha256(files['manifest.json']).hexdigest(),
                      'errors': errs, 'scope': 'integrity only'}))
    return 1 if errs else 0


if __name__ == '__main__':
    sys.exit(main())
