#!/usr/bin/env python3
"""Artifact/source/copy-build intake, not an independent manuscript gate."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[4]
BASE = PROJECT / 'frontier/campaigns/2026-10-14'
ROOT = BASE / 't088p133-manuscript-r2'
R1 = BASE / 't088p133-manuscript-r1'
LEAN = PROJECT.parent / 'dlp-research/.tools/lean-4.34.1-linux/bin/lean'
CACHE = BASE / 'formal/.lake/packages'
ANCHORS = {
    'final': '7a98b6fc2f55ddc21187b77dac24538e193492732e36fe0f07fe4c5bf3c29672',
    'manifest': 'c726a7a8329271f9a903cb88b230217820574f1c5e35248ed3670becacc68d68',
    'report': '11a45a886b1cba9262809a8cfce0df5842ead74993efb0730400ab4702bab6f1',
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def record(p):
    s = p.lstat()
    r = {'mode': stat.S_IMODE(s.st_mode), 'nlink': s.st_nlink}
    if p.is_symlink():
        r.update(kind='symlink', target=str(p.readlink()))
    elif p.is_dir():
        r['kind'] = 'directory'
    else:
        r.update(kind='file', bytes=s.st_size, sha256=sha(p))
    return r


def snap(root):
    return {str(p.relative_to(root)): record(p) for p in [root, *root.rglob('*')]}


def run(args):
    r = subprocess.run(args, text=True, capture_output=True)
    assert r.returncode == 0, (args, r.returncode, r.stderr)
    return {'exit': r.returncode, 'stdout': r.stdout, 'stderr': r.stderr}


def verify(root):
    args = [sys.executable, '-B', str(root / 'packet/public/verify.py'), str(root)]
    for k, h in ANCHORS.items():
        args += ['--' + k + '-sha256', h]
    return run(args)


def named_inventory(path, root):
    j = json.loads(path.read_text())
    for rel, m in j['files'].items():
        p = root / rel
        r = record(p)
        assert r['kind'] == 'file' and r['nlink'] == 1, rel
        assert all(r[k] == m[k] for k in ('bytes', 'mode', 'sha256')), rel
    return len(j['files'])


def main():
    before = snap(ROOT)
    result = {'kind': 'PARENT_FINAL_DRAFT_INTAKE_NOT_MANUSCRIPT_REVIEW', 'anchors': ANCHORS}
    result['verification'] = verify(ROOT)
    final = json.loads((ROOT / 'FINAL.json').read_text())
    for rel, key in [('private/MANIFEST-r2.json', 'private_evidence_manifest_sha256'),
                     ('private/build-cache-manifest-r2.json', 'private_cache_inventory_sha256')]:
        assert sha(ROOT / rel) == final[key]
    result['separate_private_named_files'] = named_inventory(ROOT / 'private/MANIFEST-r2.json', ROOT)
    result['separate_engine_cache_named_files'] = named_inventory(ROOT / 'private/build-cache-manifest-r2.json', ROOT)
    originals = json.loads((ROOT / 'work/originals-before.json').read_text())
    assert len(originals) == 3682
    assert originals == json.loads((ROOT / 'work/originals-end.json').read_text())
    for rel, r in originals.items():
        assert record(PROJECT / rel) == r, rel
    preserved = json.loads((ROOT / 'packet/public/qa/original-preservation.json').read_text())
    for rel in preserved['whole_original_roots']:
        actual = {rel} | {p.relative_to(PROJECT).as_posix() for p in (PROJECT / rel).rglob('*')}
        expected = {p for p in originals if p == rel or p.startswith(rel + '/')}
        assert actual == expected, rel
    for rel, m in preserved['parent_named_inputs_match_earlier_copies'].items():
        assert sha(PROJECT / rel) == m['sha256'] and (PROJECT / rel).stat().st_size == m['bytes']
    origin = json.loads((ROOT / 'packet/public/formal/origin.json').read_text())
    assert len(origin) == 53
    for rel, m in origin.items():
        assert sha(ROOT / 'packet/public' / rel) == m['sha256'] == sha(PROJECT / m['original'])
    p1, p2 = R1 / 'packet/public', ROOT / 'packet/public'
    old, new = (p1 / 'main.tex').read_text(), (p2 / 'main.tex').read_text()
    delta = ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                        fromfile='r1/main.tex', tofile='r2/main.tex'))
    assert delta == (p2 / 'qa/main-r1-to-r2.diff').read_text()
    result['unchanged_environment_counts'] = {}
    for env in ('theorem', 'lemma', 'proposition', 'proof'):
        pattern = r'\\begin\{' + env + r'\}.*?\\end\{' + env + r'\}'
        a, b = re.findall(pattern, old, re.S), re.findall(pattern, new, re.S)
        assert a == b
        result['unchanged_environment_counts'][env] = len(a)
    preserved_source = json.loads((p2 / 'qa/source-preservation.json').read_text())
    for rel, h in preserved_source['unchanged_files'].items():
        assert sha(p1 / rel) == h == sha(p2 / rel)
    result.update(formal_origin_files_unchanged=53, actual_original_entries=3682,
                  whole_original_roots=len(preserved['whole_original_roots']),
                  stable_parent_inputs=len(preserved['parent_named_inputs_match_earlier_copies']),
                  actual_r1_to_r2_diff_identical=True)
    with tempfile.TemporaryDirectory(prefix='copy-', dir=HERE) as td:
        temp = Path(td)
        copy = temp / 'draft'
        copy.mkdir()
        shutil.copytree(ROOT / 'packet', copy / 'packet')
        for name in ('FINAL.json', 'REPORT.md'):
            shutil.copy2(ROOT / name, copy / name)
        packet_before = snap(copy / 'packet')
        result['exact_support'] = run([sys.executable, '-B', str(copy / 'packet/public/support/reproduce.py'),
                                       str(copy / 'build/checks')])
        assert (copy / 'build/checks/witness-tables.tex').read_bytes() == (p2 / 'witness-tables.tex').read_bytes()
        result['copied_controls'] = run([sys.executable, '-B', str(copy / 'packet/public/support/integrity_controls.py'),
                                         str(copy), str(copy / 'work/parent-controls')])
        control = json.loads((copy / 'work/parent-controls/results.json').read_text())
        assert len(control['results']) == 12
        assert all(c['actual_exit'] == c['expected_exit'] and c['read_only_snapshot_equal'] for c in control['results'])
        result['control_cases'] = control['results']
        # Separate public-source context: no manuscript TeX/PDF, author or private inputs.
        context = temp / 'formal-only'
        cp = context / 'packet/public'
        (cp / 'support').mkdir(parents=True)
        shutil.copytree(p2 / 'formal', cp / 'formal')
        shutil.copy2(p2 / 'support/formal_reproduce.py', cp / 'support/formal_reproduce.py')
        formal_before = snap(context / 'packet')
        log = run([sys.executable, '-B', str(cp / 'support/formal_reproduce.py'),
                   '--lean', str(LEAN), '--cache', str(CACHE), '--output', str(context / 'build/work/fresh')])
        (HERE / 'formal-build.log').write_text(log['stdout'] + log['stderr'])
        receipt = json.loads((context / 'build/work/fresh/receipt.json').read_text())
        assert receipt['status'] == 'REPRODUCED_56_DECLARATIONS'
        assert (receipt['support'], receipt['controls'], receipt['audit']) == (21, 20, 15)
        assert len(receipt['exact_configurations']) == 10 and len(receipt['semantic_mutations']) == 2
        assert all(c['support_compiled'] and c['contract_rejected'] for c in receipt['semantic_mutations'])
        assert receipt['historical_type_logs_byte_identical']
        result['formal_reproduction'] = {
            k: receipt[k] for k in ('status', 'support', 'controls', 'audit', 'full_theorem_formalized',
                'trust', 'historical_type_logs_byte_identical', 'semantic_mutations', 'source_hashes')}
        result['formal_reproduction'].update(exact_configurations=10, execution_context='public formal copies plus wrapper only',
            lean=str(LEAN), cache=str(CACHE), packet_unchanged=snap(context / 'packet') == formal_before)
        assert result['formal_reproduction']['packet_unchanged']
        result['post_controls_verification'] = verify(copy)
        assert snap(copy / 'packet') == packet_before
    for rel, r in originals.items():
        assert record(PROJECT / rel) == r, rel
    assert snap(ROOT) == before
    result.update(all_expected=True, public_payload_files=147, public_directories=22, copied_cases=12,
        patterns=10, sparse_coefficients=248, pdf_sha256=sha(p2 / 'output/pdf/main.pdf'),
        whole_actual_draft_unchanged=True, named_originals_unchanged=True,
        formal_integration='INDEPENDENTLY_ADOPTED_SCOPED_SUPPORT_UNCHANGED', manuscript_gate=False)
    result['limits'] = (
        'Public seal:147 files/22 dirs; separately FINAL-bound36 private named files and416 engine/cache files '
        'authenticated outside public-verifier coverage, not exact private/build tree coverage. 3682 named entries '
        'and exact six original-root path sets plus six parent inputs match; hash inventory is not body reading. '
        'New relative formal wrapper compiles56 declarations from a formal-only copied context with explicit trusted '
        'Lean/precompiled cache; ten rational cases and two added-premise semantic mutations reproduce. No OS sandbox, '
        'clean dependency-source build or complete Lean binary-cache authentication. Exact10-pattern/248-term support '
        'and12 read-only copied artifact fixtures reproduce. Parent does not rebuild this PDF here; implementer '
        '20-page visual/same-cache identity remains attributed. Parent layout intake is sampled only; full independent '
        'manuscript review and verified local release remain required.')
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('all_expected', 'public_payload_files', 'public_directories',
        'separate_private_named_files', 'separate_engine_cache_named_files', 'actual_original_entries',
        'formal_origin_files_unchanged', 'copied_cases', 'whole_actual_draft_unchanged', 'manuscript_gate')}))


if __name__ == '__main__':
    main()
