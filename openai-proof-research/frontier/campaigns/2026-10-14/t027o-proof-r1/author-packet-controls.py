#!/usr/bin/env python3
"""MIT. Reviewer identity controls for the frozen T027O author packet.

Reads the author packet and canonical tree in place (read-only). Every mutation runs on a
disposable copy under /var/tmp. Never reseals or edits the author packet.
"""
import hashlib, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(os.path.abspath(__file__)).parent
REPO = HERE.parents[3]
AUTHOR = HERE.parent / 'fresh-arithmetic-discovery-r36'
SRC = 'Integral-points-on-character-varieties-of-curves-September-25-2026'
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
ANCHORS = {
    'manifest.json': '2127e23fd2698f75585c70ec4be93d599bb449c8d0f20a4bf6013a00cd7f0199',
    'verify.py': '2ad360c2d5d89bcd6afe7f875a6097bb55639bc37d62ff258a2582d867c5f5e8',
    'candidate027o.md': 'e5812790dc336e2184ffbee58882fb154175554b9e23e0cacedeecac6bf48867',
    'scope027o.md': '0f53abf319dfde7e8e1e88be77f98a5e0c423dcb0f9ffd99993088dc59b5cda2',
    'source-and-credit.md': 'e1086b79e6d2d76b290fdd4d8ce9969137fe0f76ee5aea1dfcd01886aade7391',
}

def sha(b): return hashlib.sha256(b).hexdigest()
def gitblob(b): return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()

def canonical_comparison():
    raw = (REPO / 'sources/preprints-tree.json').read_bytes()
    if sha(raw) != TREE_SHA: raise SystemExit('canonical tree anchor mismatch')
    t = json.loads(raw)
    prefix = 'preprints/' + SRC + '/'
    canon = {e['path'][len(prefix):]: e for e in t['tree'] if e['path'].startswith(prefix) and e['type'] == 'blob'}
    base = AUTHOR / 'private/preprints' / SRC
    local = {}
    for root, _, files in os.walk(base):
        for f in files:
            p = Path(root) / f; b = p.read_bytes(); local[p.relative_to(base).as_posix()] = (gitblob(b), len(b))
    rows = {k: ('MATCH' if k in local and local[k] == (v['sha'], v.get('size')) else ('ABSENT' if k not in local else 'MISMATCH'))
            for k, v in sorted(canon.items())}
    return {'tree_sha256': TREE_SHA, 'tree_entries': len(t['tree']), 'truncated': t['truncated'],
            'canonical_blobs_in_source_dir': len(canon), 'per_path': rows,
            'extra_local': sorted(set(local) - set(canon)),
            'non_pdf_all_match': all(v == 'MATCH' for k, v in rows.items() if not k.lower().endswith('.pdf')),
            'absent_only_pdf': all(k.lower().endswith('.pdf') for k, v in rows.items() if v != 'MATCH')}

def run(packet, anchor):
    c = subprocess.run([sys.executable, '-B', str(packet / 'verify.py'), anchor], capture_output=True, text=True)
    return {'returncode': c.returncode, 'output': (c.stdout + c.stderr).strip()}

def reseal(copy):
    m = json.loads((copy / 'manifest.json').read_bytes())
    files = {}
    for root, dirs, fs in os.walk(copy):
        for f in fs:
            p = Path(root) / f; rel = p.relative_to(copy).as_posix()
            if rel != 'manifest.json': files[rel] = {'bytes': p.stat().st_size, 'sha256': sha(p.read_bytes())}
    m['files'] = files
    (copy / 'manifest.json').write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')
    return sha((copy / 'manifest.json').read_bytes())

def copied_controls():
    anchor = ANCHORS['manifest.json']
    scratch = Path(tempfile.mkdtemp(prefix='t027o-proof-r1-', dir='/var/tmp'))
    cases = {}
    names = ['unchanged_copy', 'wrong_anchor', 'payload_byte', 'missing_file', 'extra_file', 'extra_empty_directory',
             'file_symlink', 'root_symlink', 'hardlink', 'fifo', 'nested_manifest', 'self_reseal_old_anchor',
             'source_byte_reseal_new_anchor', 'primary_text_reseal_new_anchor', 'receipt_drop_reseal_new_anchor']
    try:
        for name in names:
            case = scratch / name; case.mkdir(); copy = case / 'packet'
            shutil.copytree(AUTHOR, copy, symlinks=True)
            target, used, expect_ok = copy, anchor, name == 'unchanged_copy'
            if name == 'wrong_anchor': used = '1' * 64
            elif name == 'payload_byte':
                p = copy / 'candidate027o.md'; b = bytearray(p.read_bytes()); b[100] ^= 1; p.write_bytes(bytes(b))
            elif name == 'missing_file': (copy / 'scope027o.md').unlink()
            elif name == 'extra_file': (copy / 'extra.txt').write_text('x')
            elif name == 'extra_empty_directory': (copy / 'extra-dir').mkdir()
            elif name == 'file_symlink':
                (copy / 'scope027o.md').unlink(); (copy / 'scope027o.md').symlink_to(AUTHOR / 'scope027o.md')
            elif name == 'root_symlink':
                target = case / 'link'; target.symlink_to(copy, target_is_directory=True)
            elif name == 'hardlink':
                out = case / 'outside'; shutil.copyfile(copy / 'scope027o.md', out); (copy / 'scope027o.md').unlink(); os.link(out, copy / 'scope027o.md')
            elif name == 'fifo': os.mkfifo(copy / 'pipe')
            elif name == 'nested_manifest': (copy / 'provenance/manifest.json').write_text('{}')
            elif name == 'self_reseal_old_anchor':
                with (copy / 'candidate027o.md').open('a') as f: f.write('\nmutation\n')
                reseal(copy)
            elif name == 'source_byte_reseal_new_anchor':
                p = copy / 'private/preprints' / SRC / 'build/sections/surfaces.tex'
                p.write_bytes(p.read_bytes().replace(b'irreducible', b'reducible', 1)); used = reseal(copy)
            elif name == 'primary_text_reseal_new_anchor':
                p = copy / 'private/primary/coccia-litt.txt'; p.write_bytes(p.read_bytes() + b'\n'); used = reseal(copy)
            elif name == 'receipt_drop_reseal_new_anchor':
                p = copy / 'source027-receipts.json'; r = json.loads(p.read_text()); p.write_text(json.dumps(r[1:], indent=2)); used = reseal(copy)
            res = run(target, used); res['expected_pass'] = expect_ok
            res['as_expected'] = (res['returncode'] == 0) == expect_ok
            cases[name] = res
            shutil.rmtree(case)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    return cases

def main():
    anchors = {k: {'expected': v, 'actual': sha((AUTHOR / k).read_bytes())} for k, v in ANCHORS.items()}
    for v in anchors.values(): v['match'] = v['expected'] == v['actual']
    if not all(v['match'] for v in anchors.values()):
        print(json.dumps({'status': 'FAIL', 'anchors': anchors}, indent=1)); sys.exit(1)
    in_place_positive = run(AUTHOR, ANCHORS['manifest.json'])
    in_place_wrong = run(AUTHOR, '0' * 64)
    canon = canonical_comparison()
    cases = copied_controls()
    ok = (in_place_positive['returncode'] == 0 and in_place_wrong['returncode'] == 1 and canon['non_pdf_all_match']
          and canon['absent_only_pdf'] and not canon['extra_local'] and all(c['as_expected'] for c in cases.values()))
    print(json.dumps({'status': 'PASS' if ok else 'FAIL', 'external_anchors': anchors,
                      'author_verify_in_place': in_place_positive, 'author_verify_wrong_anchor': in_place_wrong,
                      'canonical_source_comparison': canon, 'copied_controls_under_var_tmp': cases,
                      'note': 'Identity support only; certifies no proof, contribution or novelty.'}, indent=1))
    sys.exit(0 if ok else 1)

if __name__ == '__main__': main()
