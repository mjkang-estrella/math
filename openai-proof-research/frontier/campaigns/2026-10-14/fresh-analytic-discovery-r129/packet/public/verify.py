#!/usr/bin/env python3
"""Read-only integrity verifier for analytic r129 (bytes and inventory only; no mathematical gate). MIT.

Requires the SHA256 of ROOT/FINAL.json and of ROOT/REPORT.md, both supplied detached on the command line.
"""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_ENTRIES = 13223
HEX64 = re.compile('[0-9a-f]{64}')


class Reject(Exception):
    pass


def check(ok, msg):
    if not ok:
        raise Reject(msg)


def h256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def plain_file(path):
    check(not path.is_symlink(), 'symlink: ' + str(path))
    check(path.exists() and stat.S_ISREG(path.lstat().st_mode), 'missing or irregular file: ' + str(path))


def rel_path(s):
    check(isinstance(s, str) and s != '' and '\\' not in s, 'malformed path')
    p = PurePosixPath(s)
    check(not p.is_absolute() and '..' not in p.parts and p.as_posix() == s, 'noncanonical path: ' + s)
    return s


def walk(base):
    files, dirs = {}, ['.']
    stack = [base]
    while stack:
        d = stack.pop()
        for e in sorted(os.scandir(d), key=lambda e: e.name):
            p = Path(e.path)
            rel = p.relative_to(base).as_posix()
            check(not e.is_symlink(), 'symlink in packet: ' + rel)
            if e.is_dir(follow_symlinks=False):
                dirs.append(rel)
                stack.append(p)
                continue
            check(e.is_file(follow_symlinks=False), 'special file in packet: ' + rel)
            check(p.lstat().st_nlink == 1, 'hard link in packet: ' + rel)
            files[rel] = {'bytes': p.lstat().st_size, 'sha256': h256(p)}
    return files, sorted(dirs)


def verify(root, final_hash, report_hash):
    check(HEX64.fullmatch(final_hash or '') is not None, 'detached FINAL hash malformed')
    check(HEX64.fullmatch(report_hash or '') is not None, 'detached REPORT hash malformed')
    check(root.is_dir() and not root.is_symlink(), 'root is not a plain directory')
    pk = root / 'packet'
    check(pk.is_dir() and not pk.is_symlink(), 'packet is not a plain directory')
    for name in ('FINAL.json', 'REPORT.md', 'packet/MANIFEST.json'):
        plain_file(root / name)
    check(h256(root / 'FINAL.json') == final_hash, 'detached FINAL mismatch')
    check(h256(root / 'REPORT.md') == report_hash, 'detached REPORT mismatch')

    final = json.loads((root / 'FINAL.json').read_text())
    check(final.get('schema') == 1 and final.get('pin') == PIN, 'FINAL schema/pin mismatch')
    check(final.get('status') == 'PREFREEZE' and final.get('frozen') is False and final.get('nominee') is None,
          'FINAL status mismatch')
    check(final.get('report_sha256') == report_hash, 'FINAL does not bind REPORT')
    check(h256(pk / 'MANIFEST.json') == final.get('manifest_sha256'), 'FINAL does not bind MANIFEST')

    man = json.loads((pk / 'MANIFEST.json').read_text())
    check(man.get('schema') == 1 and man.get('pin') == PIN, 'MANIFEST schema/pin mismatch')
    want = {}
    for rec in man['files']:
        s = rel_path(rec['path'])
        check(s != 'MANIFEST.json' and s not in want, 'duplicate or self entry: ' + s)
        want[s] = {'bytes': rec['bytes'], 'sha256': rec['sha256']}
    wdirs = man['directories']
    check(wdirs == sorted(set(wdirs)) and '.' in wdirs, 'MANIFEST directory list malformed')
    for s in wdirs:
        rel_path(s)
    have, hdirs = walk(pk)
    have.pop('MANIFEST.json', None)
    check(have == want, 'payload inventory or hash mismatch')
    check(hdirs == wdirs, 'directory inventory mismatch')

    for key, rel in (('public_report_sha256', 'packet/public/report.md'),
                     ('screens_sha256', 'packet/public/screens.md'),
                     ('reading_limits_sha256', 'packet/public/reading-limits.md')):
        check(h256(root / rel) == final.get(key), key + ' binding mismatch')

    tp = pk / 'private/context/preprints-tree.json'
    check(h256(tp) == final.get('tree_sha256'), 'tree binding mismatch')
    tree = json.loads(tp.read_text())
    check(tree.get('truncated') is False and len(tree['tree']) == TREE_ENTRIES, 'tree incomplete or truncated')
    index = {e['path']: e for e in tree['tree']}
    check(len(index) == TREE_ENTRIES, 'duplicate tree paths')
    up = json.loads((pk / 'private/context/upstream.json').read_text())
    check(up.get('commit') == PIN, 'upstream pin mismatch')

    reg = json.loads((pk / 'private/upstream/canonical-register.json').read_text())
    seen, kept = set(), 0
    for rec in reg:
        c = rec['canonical']
        s = c['path']
        check(s not in seen, 'duplicate canonical record')
        seen.add(s)
        check(index.get(s) == c and c.get('type') == 'blob', 'canonical metadata mismatch: ' + s)
        check(rec['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + s, 'raw URL mismatch')
        local = rel_path(rec['local'])
        check(local == 'packet/private/upstream/' + s, 'local path mismatch: ' + s)
        p = root / local
        if rec['retained']:
            plain_file(p)
            b = p.read_bytes()
            check(len(b) == rec['bytes'] == c['size'], 'body size mismatch: ' + s)
            check(hashlib.sha256(b).hexdigest() == rec['sha256'], 'body SHA256 mismatch: ' + s)
            blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
            check(blob == c['sha'], 'Git blob mismatch: ' + s)
            kept += 1
        else:
            check(not p.exists() and not p.is_symlink(), 'removed body present: ' + s)
    check(len(reg) == final.get('canonical_acquired') and kept == final.get('canonical_retained'),
          'canonical counts mismatch')

    copies = 0
    for name in ('private/history/register.json', 'private/context/register.json'):
        for rec in json.loads((pk / name).read_text()):
            p = root / rel_path(rec['local'])
            plain_file(p)
            check(p.stat().st_size == rec['bytes'] and h256(p) == rec['sha256'], 'copied evidence mismatch: ' + rec['local'])
            copies += 1
    check(copies == final.get('copied_evidence'), 'copied evidence count mismatch')

    return {'status': 'INTEGRITY_ONLY_OK', 'mathematical_gate': False, 'payloads': len(have),
            'directories': len(hdirs), 'canonical_acquired': len(reg), 'canonical_retained': kept,
            'copied_evidence': copies, 'final_sha256': final_hash, 'report_sha256': report_hash}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    try:
        out = verify(a.root, a.final_sha256, a.report_sha256)
    except Exception as e:
        print('REJECT: ' + str(e), file=sys.stderr)
        return 1
    print(json.dumps(out, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
