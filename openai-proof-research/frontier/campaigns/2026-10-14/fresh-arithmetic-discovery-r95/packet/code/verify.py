#!/usr/bin/env python3
"""Read-only artifact verifier for arithmetic r95. Detached anchors must be supplied from outside the packet."""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path

sys.dont_write_bytecode = True
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
DENIED = {'os.remove', 'os.rename', 'os.mkdir', 'os.rmdir', 'os.chmod', 'os.chown', 'os.link', 'os.symlink',
          'os.truncate', 'os.utime', 'subprocess.Popen', 'os.system', 'socket.connect', 'shutil.rmtree'}


def readonly(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (
                isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
            raise RuntimeError('write denied')
    if event in DENIED:
        raise RuntimeError('mutation/network denied: ' + event)


sys.addaudithook(readonly)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def safe(base, name):
    p = Path(name)
    need(not p.is_absolute() and '..' not in p.parts and str(p) == name, 'unsafe path ' + name)
    return base / p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--tree', required=True, type=Path)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    root = a.root
    packet = root / 'packet'
    need(sha(a.tree) == TREE, 'preprints tree mismatch')
    need(sha(root / 'FINAL.json') == a.final_sha256, 'detached FINAL mismatch')
    need(sha(root / 'REPORT.md') == a.report_sha256, 'detached REPORT mismatch')
    final = json.loads((root / 'FINAL.json').read_text())
    need(final['report_sha256'] == a.report_sha256, 'FINAL does not bind REPORT')
    need(final['status'] == 'PREFREEZE' and final['nominee'] is None and final['frozen_target'] is None, 'status mismatch')
    need(final['pin'] == PIN and final['tree_sha256'] == TREE, 'pin mismatch')
    for key, rel in [('manifest_sha256', 'MANIFEST.json'), ('verifier_sha256', 'code/verify.py'),
                     ('controls_sha256', 'code/controls.py'), ('public_report_sha256', 'public/report.md')]:
        need(sha(packet / rel) == final[key], 'FINAL binding mismatch: ' + rel)
    manifest = json.loads((packet / 'MANIFEST.json').read_text())
    need(manifest['status'] == 'PREFREEZE' and manifest['round'] == 'fresh-arithmetic-discovery-r95', 'manifest header')

    files, dirs = {}, {}
    for base, ds, fs in os.walk(packet, followlinks=False):
        bp = Path(base)
        rel = bp.relative_to(packet).as_posix()
        s = bp.lstat()
        need(stat.S_ISDIR(s.st_mode), 'non-directory walk entry ' + rel)
        dirs[rel] = stat.S_IMODE(s.st_mode)
        for d in ds:
            need(not (bp / d).is_symlink(), 'symlinked directory ' + d)
        for f in fs:
            p = bp / f
            s = p.lstat()
            r = p.relative_to(packet).as_posix()
            need(stat.S_ISREG(s.st_mode), 'not a regular file: ' + r)
            need(s.st_nlink == 1, 'hard link: ' + r)
            if r == 'MANIFEST.json':
                continue
            files[r] = {'bytes': s.st_size, 'mode': stat.S_IMODE(s.st_mode), 'sha256': sha(p)}
    need(dirs == manifest['directories'], 'directory set or mode mismatch')
    need(set(files) == set(manifest['files']), 'file set mismatch')
    for r, rec in files.items():
        need(rec == manifest['files'][r], 'file record mismatch: ' + r)

    tree = {e['path']: e for e in json.loads(a.tree.read_text())['tree']}
    sources = json.loads((packet / 'public/source-register.json').read_text())
    seen = set()
    for x in sources:
        e = tree.get(x['path'])
        need(e is not None and e['type'] == 'blob' and e['sha'] == x['git_blob'] and e['size'] == x['bytes'], 'tree record mismatch ' + x['path'])
        need(x['path'] not in seen, 'duplicate source')
        seen.add(x['path'])
        need(x['raw_url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + x['path'], 'raw URL mismatch')
        b = safe(packet, x['local']).read_bytes()
        need(len(b) == x['bytes'] and hashlib.sha256(b).hexdigest() == x['sha256'], 'source body mismatch ' + x['path'])
        need(hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == x['git_blob'], 'git blob mismatch ' + x['path'])
    primaries = json.loads((packet / 'public/primary-register.json').read_text())
    for x in primaries:
        need(sha(safe(packet, x['pdf'])) == x['pdf_sha256'] and sha(safe(packet, x['text'])) == x['text_sha256'], 'primary mismatch ' + x['pdf'])
    context = json.loads((packet / 'public/context-register.json').read_text())
    for x in context:
        p = safe(packet, x['local'])
        need(sha(p) == x['sha256'] and p.stat().st_size == x['bytes'], 'context mismatch ' + x['local'])
    status = json.loads((packet / 'public/status.json').read_text())
    need(status['status'] == 'PREFREEZE' and status['nominee'] is None and status['author_proof'] is None, 'status.json mismatch')
    print(json.dumps({'artifact_verification': 'PASS', 'payload_files_excluding_manifest': len(files),
                      'directories_including_packet_root': len(dirs), 'canonical_sources': len(sources),
                      'primary_pairs': len(primaries), 'context_history_copies': len(context),
                      'runner': 'Factory Droid Opus 5.5 high', 'mathematical_gate': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
