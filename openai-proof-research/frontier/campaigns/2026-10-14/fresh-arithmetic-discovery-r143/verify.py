"""Read-only packet verification. All three detached expected hashes are required."""
import argparse, hashlib, json, os
from pathlib import Path, PurePosixPath


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    root = Path(a.root).resolve()
    errors = []
    anchors = {'FINAL.md': a.final_sha256, 'MANIFEST.json': a.manifest_sha256,
               'REPORT.md': a.report_sha256}
    for name, expected in anchors.items():
        p = root / name
        if p.is_symlink() or not p.is_file():
            errors.append('missing/nonregular anchor: ' + name)
        elif digest(p) != expected:
            errors.append('detached anchor mismatch: ' + name)
    if errors:
        print(json.dumps({'artifact_ok': False, 'errors': errors})); return 1
    m = json.loads((root / 'MANIFEST.json').read_text())
    entries = m['files']
    names = set()
    for e in entries:
        rel = e['path']; posix = PurePosixPath(rel)
        if posix.is_absolute() or '..' in posix.parts or rel != posix.as_posix() or rel in names:
            errors.append('invalid/duplicate path: ' + rel); continue
        names.add(rel); p = root / rel
        if p.is_symlink() or not p.is_file() or any(x.is_symlink() for x in p.parents if x != root and root in x.parents):
            errors.append('missing/nonregular payload: ' + rel); continue
        if p.stat().st_size != e['bytes'] or digest(p) != e['sha256']:
            errors.append('payload mismatch: ' + rel)
    actual = set()
    for d, dirs, files in os.walk(root, followlinks=False):
        for n in dirs:
            if (Path(d) / n).is_symlink(): errors.append('symlink directory')
        for n in files:
            actual.add((Path(d) / n).relative_to(root).as_posix())
    expected = names | {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
    # ANCHORS.json is an optional untrusted receipt; supplied CLI anchors are authoritative.
    missing = (names | {'MANIFEST.json', 'REPORT.md'}) - actual
    extra = actual - expected
    if missing: errors.append('missing files: ' + ', '.join(sorted(missing)))
    if extra: errors.append('extra files: ' + ', '.join(sorted(extra)))
    print(json.dumps({'artifact_ok': not errors, 'payload_files': len(entries),
                      'errors': errors, 'scope': 'bytes and selection only; no mathematical gate'}))
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
