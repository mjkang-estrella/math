#!/usr/bin/env python3
"""Read-only artifact verifier for arithmetic r99.

Detached FINAL and REPORT anchors must be supplied from outside the packet.
This checks file identity and register consistency only; it is not a
mathematical gate.
"""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path

sys.dont_write_bytecode = True
ROUND = 'fresh-arithmetic-discovery-r99'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
FROZEN = '2a39e2a3410a79812e3e48478fa892d507e163fcd739fd409173219c7c5a23b7'
STATUS = 'AUTHOR_PROOF_NOMINEE'
RAW = 'https://raw.githubusercontent.com/openai/math/' + PIN + '/'
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
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def safe(base, name):
    p = Path(name)
    need(not p.is_absolute() and '..' not in p.parts and str(p) == name, 'unsafe path ' + name)
    return base / p


def git_blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--tree', required=True, type=Path)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    root, packet = a.root, a.root / 'packet'
    need(sha(a.tree) == TREE, 'preprints tree mismatch')
    need(sha(root / 'FINAL.json') == a.final_sha256, 'detached FINAL mismatch')
    need(sha(root / 'REPORT.md') == a.report_sha256, 'detached REPORT mismatch')
    final = json.loads((root / 'FINAL.json').read_text())
    need(final['report_sha256'] == a.report_sha256, 'FINAL does not bind REPORT')
    need(final['round'] == ROUND and final['status'] == STATUS, 'FINAL header mismatch')
    need(final['pin'] == PIN and final['tree_sha256'] == TREE, 'pin mismatch')
    need(final['scope_freeze_sha256'] == FROZEN, 'frozen scope anchor mismatch')
    need(sha(packet / 'public/scope-freeze.md') == FROZEN, 'frozen scope bytes changed')
    for key, rel in [('manifest_sha256', 'MANIFEST.json'), ('verifier_sha256', 'code/verify.py'),
                     ('controls_sha256', 'code/controls.py'), ('public_report_sha256', 'public/report.md'),
                     ('proof_sha256', 'public/proof.md')]:
        need(sha(packet / rel) == final[key], 'FINAL binding mismatch: ' + rel)
    manifest = json.loads((packet / 'MANIFEST.json').read_text())
    need(manifest['status'] == STATUS and manifest['round'] == ROUND, 'manifest header')

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
    reg = json.loads((packet / 'public/source-register.json').read_text())
    need(reg['pin'] == PIN and reg['tree_sha256'] == TREE and reg['truncated'] is False, 'source register header')
    need(reg['tree_entries'] == len(tree), 'tree entry count mismatch')
    seen, locals_ = set(), set()
    for x in reg['retained']:
        e = tree.get(x['upstream_path'])
        need(e is not None and e['type'] == 'blob' and e['sha'] == x['git_blob'] and e['size'] == x['size'],
             'tree record mismatch ' + x['upstream_path'])
        need(x['upstream_path'] not in seen, 'duplicate source')
        seen.add(x['upstream_path'])
        need(x['raw_url'] == RAW + x['upstream_path'] and x.get('read_extent'), 'source record incomplete')
        need(x['local'] == 'private/upstream/' + x['upstream_path'], 'source local path mismatch')
        b = safe(packet, x['local']).read_bytes()
        need(len(b) == x['size'] and hashlib.sha256(b).hexdigest() == x['sha256'], 'source body mismatch ' + x['upstream_path'])
        need(git_blob(b) == x['git_blob'], 'git blob mismatch ' + x['upstream_path'])
        locals_.add(x['local'])
    need(reg['removed'] == [], 'unexpected removed-source records')
    upstream_files = {r for r in files if r.startswith('private/upstream/')}
    need(upstream_files == locals_, 'unregistered upstream file')

    log = [json.loads(line) for line in (packet / 'public/fetch-log.jsonl').read_text().splitlines()]
    need({x['path'] for x in log} == seen and len(log) == len(seen) and all(x['blob_match'] for x in log), 'fetch log mismatch')
    for x in log:
        r = next(y for y in reg['retained'] if y['upstream_path'] == x['path'])
        need(x['got_blob'] == r['git_blob'] and x['tree_blob'] == r['git_blob'] and x['sha256'] == r['sha256']
             and x['size'] == r['size'] and x['url'] == r['raw_url'], 'fetch receipt mismatch')

    primary = json.loads((packet / 'public/primary-register.json').read_text())
    prim = set()
    for x in primary:
        p = safe(packet, x['local'])
        need(x['local'].startswith('private/primary/') and x['local'] not in prim, 'primary path')
        need(sha(p) == x['sha256'] and p.stat().st_size == x['size'], 'primary mismatch ' + x['local'])
        need(x.get('citation') and x.get('read_extent') and x.get('identifiers', {}).get('url'), 'primary record incomplete')
        prim.add(x['local'])
    need({r for r in files if r.startswith('private/primary/')} == prim, 'unregistered primary file')

    history = set()
    for x in json.loads((packet / 'public/context-register.json').read_text())['copies']:
        p = safe(packet, x['local'])
        need(x['local'].startswith('private/history/'), 'context copy outside history dir')
        need(sha(p) == x['sha256'] and p.stat().st_size == x['size'], 'context mismatch ' + x['local'])
        history.add(x['local'])
    need({r for r in files if r.startswith('private/history/')} == history, 'unregistered history file')
    need(not ({r for r in files if r.startswith('private/')} - upstream_files - history - prim), 'unregistered private file')

    status = json.loads((packet / 'public/status.json').read_text())
    need(status['round'] == ROUND and status['pin'] == PIN and status['status'] == STATUS, 'status.json header')
    need(status['scope_freeze_sha256'] == FROZEN and status['self_gates'] is None and status['count'] is None,
         'status.json mismatch')
    print(json.dumps({'artifact_verification': 'PASS', 'payload_files_excluding_manifest': len(files),
                      'directories_including_packet_root': len(dirs), 'retained_sources': len(reg['retained']),
                      'primary_files': len(primary), 'context_history_copies': len(history),
                      'frozen_scope_sha256': FROZEN, 'runner': 'Factory Droid claude-opus-5-5 high',
                      'mathematical_gate': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
