"""Read-only artifact verifier. Explicit detached anchors are mandatory.
This establishes no mathematical verdict. Run with python -I -B.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, re, stat

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def safe_name(s):
    p = PurePosixPath(s)
    return isinstance(s, str) and s == str(p) and not p.is_absolute() and bool(p.parts) and all(x not in ('', '.', '..') for x in p.parts) and '\\' not in s

def verify(root, final_sha, manifest_sha, report_sha):
    assert root.is_dir() and not root.is_symlink(), 'root'
    anchors = {'FINAL.md': final_sha, 'MANIFEST.json': manifest_sha, 'REPORT.md': report_sha}
    for name, sha in anchors.items():
        assert re.fullmatch('[0-9a-f]{64}', sha), 'explicit anchor format'
        assert digest(root / name) == sha, 'detached anchor: ' + name
    manifest = json.loads((root / 'MANIFEST.json').read_bytes())
    entries = manifest['entries']
    names = [e['path'] for e in entries]
    assert names == sorted(set(names)), 'sorted exact manifest'
    assert all(safe_name(n) for n in names), 'unsafe selection path'
    selected = json.loads((root / 'selection.json').read_bytes())['files']
    assert selected == names, 'selection mismatch'
    assert 'selection.json' in names and 'verify_packet.py' in names, 'self binding'
    final = (root / 'FINAL.md').read_text(encoding='utf8')
    assert 'Manifest SHA256: ' + manifest_sha in final, 'final manifest binding'
    assert 'Selection SHA256: ' + digest(root / 'selection.json') in final, 'final selection binding'
    detached = {'FINAL.md', 'MANIFEST.json', 'REPORT.md', 'ANCHORS.json', 'SEAL-CHECK.json'}
    assert not (set(names) & detached), 'detached/selected overlap'
    expected_dirs = {str(p) for n in names for p in PurePosixPath(n).parents if str(p) != '.'}
    actual_files, actual_dirs = set(), set()
    for base, dirs, files in os.walk(root, followlinks=False):
        for name in dirs:
            p = Path(base) / name
            assert not p.is_symlink(), 'symlink directory'
            actual_dirs.add(p.relative_to(root).as_posix())
        for name in files:
            p = Path(base) / name
            mode = p.lstat().st_mode
            assert stat.S_ISREG(mode), 'nonregular file'
            assert stat.S_IMODE(mode) == 0o444, 'file mode: ' + str(p)
            actual_files.add(p.relative_to(root).as_posix())
    assert actual_dirs == expected_dirs, 'directory surface mismatch'
    assert actual_files - detached == set(names), 'file surface mismatch'
    assert set(anchors) <= actual_files, 'missing detached files'
    for e in entries:
        p = root / e['path']
        assert e['mode'] == '0444' and p.stat().st_size == e['bytes'], 'size/mode: ' + e['path']
        assert digest(p) == e['sha256'], 'payload hash: ' + e['path']
    if (root / 'ANCHORS.json').exists():
        assert json.loads((root / 'ANCHORS.json').read_bytes()) == anchors, 'anchor sidecar mismatch'
    return {'artifact_verification': 'OK', 'selected_files': len(names), 'present_detached_files': len(actual_files & detached), 'read_only': True, 'mathematical_correctness': 'UNDISCHARGED'}

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--root', required=True, type=Path)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    print(json.dumps(verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256), sort_keys=True))
