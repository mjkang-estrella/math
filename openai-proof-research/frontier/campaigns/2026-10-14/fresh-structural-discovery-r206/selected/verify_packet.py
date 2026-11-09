#!/usr/bin/env python3
"""Read-only artifact verifier. All three detached SHA256 anchors are mandatory."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(packet, manifest, report, manifest_sha, final_sha, report_sha):
    packet, manifest, report = map(Path, (packet, manifest, report))
    assert not manifest.is_symlink() and not report.is_symlink(), "detached symlink"
    assert digest(manifest) == manifest_sha, "MANIFEST anchor mismatch"
    assert digest(report) == report_sha, "REPORT anchor mismatch"
    obj = json.loads(manifest.read_text())
    assert obj['format'] == 'r206-exact-selection-v1', "manifest format"
    expected_files, expected_dirs = {}, {}
    for row in obj['files']:
        rel = row['path']; p = PurePosixPath(rel)
        assert rel and not p.is_absolute() and '..' not in p.parts and str(p) == rel, "unsafe path"
        assert rel not in expected_files, "duplicate file"
        expected_files[rel] = row
    for row in obj['directories']:
        rel = row['path']; p = PurePosixPath(rel)
        assert rel == '' or (not p.is_absolute() and '..' not in p.parts and str(p) == rel), "unsafe directory"
        assert rel not in expected_dirs, "duplicate directory"
        expected_dirs[rel] = row
    assert 'FINAL.md' in expected_files, "FINAL absent"
    got_files, got_dirs = set(), set()
    def walk(d, rel):
        assert not d.is_symlink(), "directory symlink"
        got_dirs.add(rel)
        assert rel in expected_dirs, "extra directory"
        assert stat.S_IMODE(d.stat().st_mode) == int(expected_dirs[rel]['mode'], 8), "directory mode"
        for e in os.scandir(d):
            p = Path(e.path); name = (rel + '/' if rel else '') + e.name
            assert not e.is_symlink(), "selected symlink"
            if e.is_dir(follow_symlinks=False): walk(p, name)
            else:
                assert e.is_file(follow_symlinks=False), "nonregular file"
                got_files.add(name)
                assert name in expected_files, "extra file"
                row = expected_files[name]
                assert p.stat().st_size == row['bytes'], "size mismatch"
                assert stat.S_IMODE(p.stat().st_mode) == int(row['mode'], 8), "file mode"
                assert digest(p) == row['sha256'], "file bytes mismatch"
    walk(packet, '')
    assert got_files == set(expected_files), "missing file"
    assert got_dirs == set(expected_dirs), "missing directory"
    assert digest(packet/'FINAL.md') == final_sha, "FINAL anchor mismatch"
    return {'artifact_check':'passed','files':len(got_files),'directories':len(got_dirs),'mathematical_gate':False}

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for name in ['packet','manifest','report','manifest-sha','final-sha','report-sha']:
        p.add_argument('--'+name, required=True)
    a = p.parse_args()
    print(json.dumps(verify(a.packet,a.manifest,a.report,a.manifest_sha,a.final_sha,a.report_sha),sort_keys=True))
