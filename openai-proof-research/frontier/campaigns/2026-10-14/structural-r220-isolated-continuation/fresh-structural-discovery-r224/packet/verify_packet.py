"""Read-only exact-selection artifact verification. Not a mathematical gate."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat, sys

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise ValueError(message)

def safe_relative(value):
    require(isinstance(value, str) and value, 'empty/nonstring path')
    p = PurePosixPath(value)
    require(not p.is_absolute() and '..' not in p.parts and '.' not in p.parts
            and '\\' not in value and p.as_posix() == value, 'unsafe relative path')
    return value

def regular(p, mode):
    s = p.lstat()
    require(stat.S_ISREG(s.st_mode), 'not a regular file: '+str(p))
    require(stat.S_IMODE(s.st_mode) == mode, 'file mode mismatch: '+str(p))
    return s

def verify(root, expected_manifest, expected_final, expected_report):
    for a in (expected_manifest, expected_final, expected_report):
        require(len(a) == 64 and all(c in '0123456789abcdef' for c in a), 'invalid explicit anchor')
    manifest, report, packet = root/'MANIFEST.json', root/'REPORT.md', root/'packet'
    regular(manifest, 0o644)
    regular(report, 0o644)
    require(digest(manifest) == expected_manifest, 'MANIFEST anchor mismatch')
    require(digest(report) == expected_report, 'REPORT anchor mismatch')
    m = json.loads(manifest.read_bytes())
    require(m['schema'] == 'r224.exact-packet.v1' and m['packet_root'] == 'packet', 'manifest schema/root mismatch')
    require(stat.S_ISDIR(packet.lstat().st_mode), 'packet root is not a directory')
    require(stat.S_IMODE(packet.lstat().st_mode) == m['root_mode'], 'packet root mode mismatch')
    expected_files = {safe_relative(x['path']): x for x in m['files']}
    expected_dirs = {safe_relative(x['path']): x for x in m['directories']}
    require(len(expected_files) == len(m['files']) and len(expected_dirs) == len(m['directories']), 'duplicate selection')
    found_files, found_dirs = set(), set()
    for base, directories, files in os.walk(packet, followlinks=False):
        for name in directories:
            p = Path(base)/name
            rel = p.relative_to(packet).as_posix()
            require(stat.S_ISDIR(p.lstat().st_mode), 'non-directory/symlink in selection: '+rel)
            found_dirs.add(rel)
        for name in files:
            p = Path(base)/name
            rel = p.relative_to(packet).as_posix()
            require(stat.S_ISREG(p.lstat().st_mode), 'non-regular/symlink in selection: '+rel)
            found_files.add(rel)
    require(found_files == set(expected_files), 'exact file selection mismatch')
    require(found_dirs == set(expected_dirs), 'exact directory selection mismatch')
    for rel, row in expected_dirs.items():
        require(stat.S_IMODE((packet/rel).lstat().st_mode) == row['mode'], 'directory mode mismatch: '+rel)
    for rel, row in expected_files.items():
        p = packet/rel
        s = regular(p, row['mode'])
        require(s.st_size == row['bytes'], 'file size mismatch: '+rel)
        require(digest(p) == row['sha256'], 'file hash mismatch: '+rel)
    require('FINAL.md' in expected_files, 'FINAL not selected')
    require(digest(packet/'FINAL.md') == expected_final, 'FINAL anchor mismatch')
    return {'artifact_integrity':'verified', 'files':len(found_files), 'directories':len(found_dirs),
            'manifest_sha256':expected_manifest, 'final_sha256':expected_final,
            'outside_report_sha256':expected_report, 'mathematical_gate':False}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True, type=Path)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    args = p.parse_args()
    try:
        print(json.dumps(verify(args.root, args.manifest_sha256, args.final_sha256, args.report_sha256), sort_keys=True))
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as e:
        print(json.dumps({'artifact_integrity':'rejected', 'reason':str(e), 'mathematical_gate':False}), file=sys.stderr)
        sys.exit(1)
