#!/usr/bin/env python3
"""Copied artifact-integrity controls for analytic r127. Not mathematical gates.

Every mutation is applied to a temporary copy under controls/tmp/ and checked
by the ORIGINAL read-only verifier. Copies are removed afterwards. The original
root, excluding controls/, is hashed before and after the run.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

CONTROLS = Path(__file__).resolve().parent
ROOT = CONTROLS.parent
VERIFIER = ROOT/'packet/public/verify.py'
TMP = CONTROLS/'tmp'

def digest(b):
    return hashlib.sha256(b).hexdigest()

def tree_hash(root):
    rows = []
    for base, ds, fs in os.walk(root, followlinks=False):
        ds[:] = sorted(d for d in ds if not (Path(base) == root and d == 'controls'))
        for name in sorted(fs):
            q = Path(base)/name
            rows.append(q.relative_to(root).as_posix() + ' ' + digest(q.read_bytes()))
        for name in ds:
            rows.append((Path(base)/name).relative_to(root).as_posix() + '/')
    return digest('\n'.join(sorted(rows)).encode()), len(rows)

ORIG_FINAL = digest((ROOT/'FINAL.json').read_bytes())
ORIG_REPORT = digest((ROOT/'REPORT.md').read_bytes())

def fresh_copy(name):
    dest = TMP/name
    dest.mkdir(parents=True)
    shutil.copy2(ROOT/'FINAL.json', dest/'FINAL.json')
    shutil.copy2(ROOT/'REPORT.md', dest/'REPORT.md')
    shutil.copytree(ROOT/'packet', dest/'packet', symlinks=True)
    return dest

def flip(path):
    b = bytearray(path.read_bytes())
    b[len(b)//2] ^= 1
    path.write_bytes(bytes(b))

def reanchor(copy, edit_final=None):
    packet = copy/'packet'
    files, dirs = {}, ['.']
    for base, ds, fs in os.walk(packet, followlinks=False):
        for name in ds + fs:
            q = Path(base)/name
            rel = q.relative_to(packet).as_posix()
            if q.is_dir():
                dirs.append(rel)
            elif rel != 'MANIFEST.json':
                b = q.read_bytes()
                files[rel] = {'bytes': len(b), 'sha256': digest(b)}
    m = (json.dumps({'files': dict(sorted(files.items())), 'directories': sorted(dirs)},
                    indent=1, sort_keys=True) + '\n').encode()
    (packet/'MANIFEST.json').write_bytes(m)
    final = json.loads((copy/'FINAL.json').read_bytes())
    final['manifest_sha256'] = digest(m)
    for n in final['proof_files']:
        final['proof_files'][n] = digest((packet/'public'/n).read_bytes())
    for n in final['records']:
        final['records'][n] = digest((packet/'public'/n).read_bytes())
    if edit_final:
        edit_final(final)
    b = (json.dumps(final, indent=1, sort_keys=True) + '\n').encode()
    (copy/'FINAL.json').write_bytes(b)
    return digest(b)

def run(copy, final_hash, report_hash, probe=None):
    cmd = [sys.executable, str(VERIFIER), '--root', str(copy),
           '--final-hash', final_hash, '--report-hash', report_hash]
    if probe:
        cmd += ['--audit-probe', probe]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=600,
                       env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    return p.returncode, (p.stdout + p.stderr).strip()[-300:]

def m_none(c): return None
def m_scope(c): flip(c/'packet/public/frozen-scope.md')
def m_proof(c): (c/'packet/public/proof.md').write_text((c/'packet/public/proof.md').read_text() + '\nextra\n')
def m_extra(c): (c/'packet/public/extra.md').write_text('extra\n')
def m_drop_source(c):
    rows = json.loads((c/'packet/private/upstream/register.json').read_bytes())
    (c/'packet'/next(r['local'] for r in rows if r['retained'])).unlink()
def m_report(c): (c/'REPORT.md').write_text((c/'REPORT.md').read_text() + '\nedit\n')
def m_final_status(c):
    f = json.loads((c/'FINAL.json').read_bytes()); f['status'] = 'ACCEPTED'
    (c/'FINAL.json').write_text(json.dumps(f))
def m_reading(c): (c/'packet/public/reading-limits.md').write_text((c/'packet/public/reading-limits.md').read_text() + '\nedit\n')
def m_symlink(c): os.symlink('proof.md', c/'packet/public/link.md')
def m_tree(c): flip(c/'packet/private/context/preprints-tree.json')
def m_source_bytes(c):
    rows = json.loads((c/'packet/private/upstream/register.json').read_bytes())
    flip(c/'packet'/next(r['local'] for r in rows if r['retained']))
def m_primary(c): flip(c/'packet/private/primary/1708.00591v1.pdf')
def m_history(c): flip(c/'packet/private/history/14-i112-inverse-boundary-discovery.md')
def m_hits(c): flip(c/'packet/private/search/broad-prefreeze/hits.json')
def m_freeze(c):
    f = json.loads((c/'packet/public/freeze.json').read_bytes()); f['frozen-scope.md'] = '0'*64
    (c/'packet/public/freeze.json').write_text(json.dumps(f))
def m_verifier_copy(c): (c/'packet/public/verify.py').write_text((c/'packet/public/verify.py').read_text() + '\n# edit\n')

CASES = [
    # name, mutation, final-hash mode, report-hash mode, probe, expected exit
    ('baseline', m_none, 'orig', 'orig', None, 0),
    ('frozen-scope-byte', m_scope, 'orig', 'orig', None, 2),
    ('proof-appended', m_proof, 'orig', 'orig', None, 2),
    ('extra-payload', m_extra, 'orig', 'orig', None, 2),
    ('retained-source-removed', m_drop_source, 'orig', 'orig', None, 2),
    ('wrong-detached-final', m_none, 'wrong', 'orig', None, 2),
    ('wrong-detached-report', m_none, 'orig', 'wrong', None, 2),
    ('report-edited', m_report, 'orig', 'orig', None, 2),
    ('final-status-edited', m_final_status, 'orig', 'orig', None, 2),
    ('reanchored-record-old-detached-final', m_reading, 'reanchor-old', 'orig', None, 2),
    ('reanchored-record-new-detached-final', m_reading, 'reanchor-new', 'orig', None, 0),
    ('symlink-payload', m_symlink, 'orig', 'orig', None, 2),
    ('audit-write-probe', m_none, 'orig', 'orig', 'write', 2),
    ('audit-network-probe', m_none, 'orig', 'orig', 'network', 2),
    ('complete-tree-byte', m_tree, 'orig', 'orig', None, 2),
    ('retained-source-byte', m_source_bytes, 'orig', 'orig', None, 2),
    ('primary-pdf-byte', m_primary, 'orig', 'orig', None, 2),
    ('history-copy-byte', m_history, 'orig', 'orig', None, 2),
    ('search-hits-byte', m_hits, 'orig', 'orig', None, 2),
    ('freeze-receipt-edited', m_freeze, 'orig', 'orig', None, 2),
    ('copied-verifier-edited', m_verifier_copy, 'orig', 'orig', None, 2),
    ('self-verdict-reanchored', m_none, 'reanchor-verdict', 'orig', None, 2),
    # Consistently re-anchored copies with a NEW detached FINAL: the deeper
    # content checks, not only the manifest inventory, must reject them.
    ('reanchored-frozen-scope-byte', m_scope, 'reanchor-new', 'orig', None, 2),
    ('reanchored-proof-appended', m_proof, 'reanchor-new', 'orig', None, 0),
    ('reanchored-complete-tree-byte', m_tree, 'reanchor-new', 'orig', None, 2),
    ('reanchored-retained-source-byte', m_source_bytes, 'reanchor-new', 'orig', None, 2),
    ('reanchored-retained-source-removed', m_drop_source, 'reanchor-new', 'orig', None, 2),
    ('reanchored-primary-pdf-byte', m_primary, 'reanchor-new', 'orig', None, 2),
    ('reanchored-history-copy-byte', m_history, 'reanchor-new', 'orig', None, 2),
    ('reanchored-search-hits-byte', m_hits, 'reanchor-new', 'orig', None, 2),
    ('reanchored-freeze-receipt-edited', m_freeze, 'reanchor-new', 'orig', None, 2),
]

def main():
    if TMP.exists():
        raise SystemExit('controls/tmp already exists; refusing to reuse')
    before = tree_hash(ROOT)
    results = []
    try:
        for i, (name, mutate, fmode, rmode, probe, expected) in enumerate(CASES):
            copy = fresh_copy(f'{i:02}-{name}')
            mutate(copy)
            final_hash = ORIG_FINAL
            if fmode == 'wrong':
                final_hash = '0'*64
            elif fmode == 'reanchor-old':
                reanchor(copy)
            elif fmode == 'reanchor-new':
                final_hash = reanchor(copy)
            elif fmode == 'reanchor-verdict':
                final_hash = reanchor(copy, lambda f: f['verdicts'].update(correctness='PASS'))
            report_hash = ORIG_REPORT if rmode == 'orig' else 'f'*64
            code, tail = run(copy, final_hash, report_hash, probe)
            ok = code == expected
            if probe == 'write':
                ok = ok and not (copy/'forbidden-write').exists()
            results.append({'case': name, 'expected_exit': expected, 'exit': code,
                            'as_expected': ok, 'output_tail': tail})
            shutil.rmtree(copy)
    finally:
        if TMP.exists():
            shutil.rmtree(TMP)
    after = tree_hash(ROOT)
    receipt = {
        'artifact_integrity_only': True, 'mathematical_gate': False,
        'verifier': 'packet/public/verify.py (original, read-only)',
        'detached_final_sha256': ORIG_FINAL, 'detached_report_sha256': ORIG_REPORT,
        'cases': len(results), 'all_as_expected': all(r['as_expected'] for r in results),
        'root_tree_hash_before': before, 'root_tree_hash_after': after,
        'original_root_unchanged': before == after, 'results': results,
    }
    (CONTROLS/'receipt.json').write_text(json.dumps(receipt, indent=1) + '\n')
    print(json.dumps({k: receipt[k] for k in ['cases', 'all_as_expected', 'original_root_unchanged']}))
    sys.exit(0 if receipt['all_as_expected'] and receipt['original_root_unchanged'] else 1)

if __name__ == '__main__':
    main()
