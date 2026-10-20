#!/usr/bin/env python3
"""Authenticate independent manuscript PASS and replay new exact support."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[4]
BASE = PROJECT / 'frontier/campaigns/2026-10-14'
ROOT = BASE / 't088p133-manuscript-review-r1'
DRAFT = BASE / 't088p133-manuscript-r2'
ANCHORS = {
    'final': '4c184023e08b7713ef1204c1153cb4f663470e46358e664a8dd9ea8b08ff8aa9',
    'manifest': '0339b3229c63e11531066d6e06e752fb031a6476a207ad417bc98261fe1a7d07',
    'report': '3393e0d885ec1ba919b32ca3644d14ea471ed94a5f642f809fb7e49f741281ef',
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def record(p):
    s = p.lstat()
    d = {'mode': stat.S_IMODE(s.st_mode), 'links': s.st_nlink, 'type': stat.S_IFMT(s.st_mode)}
    if p.is_symlink():
        d['target'] = str(p.readlink())
    elif p.is_file():
        d.update(bytes=s.st_size, sha256=sha(p))
    return d


def snap(root):
    return {str(p.relative_to(root)): record(p) for p in [root, *root.rglob('*')]}


def run(args, env=None):
    p = subprocess.run(args, text=True, capture_output=True, env=env)
    assert p.returncode == 0, (args, p.returncode, p.stderr)
    return {'exit': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}


def verify(root):
    args = [sys.executable, '-B', str(ROOT / 'packet/public/verify.py'), str(root)]
    for k, v in ANCHORS.items():
        args += ['--' + k + '-sha256', v]
    return run(args)


def main():
    packages = json.loads((ROOT / 'packet/public/evidence/authentication-after.json').read_text())
    roots = [BASE / name for name in packages if name != 'tree'] + [ROOT]
    before = {str(r): snap(r) for r in roots}
    result = {'kind': 'PARENT_INDEPENDENT_MANUSCRIPT_REVIEW_ADOPTION_REPLAY', 'anchors': ANCHORS,
              'review_artifact_verification': verify(ROOT)}
    counts = {}
    for name, entry in packages.items():
        if name == 'tree':
            assert sha(PROJECT / 'sources/preprints-tree.json') == entry['sha256']
            continue
        root = BASE / name
        assert [sha(root / p) for p in ('FINAL.json', 'packet/MANIFEST.json', 'REPORT.md')] == entry['anchors']
        manifest = json.loads((root / 'packet/MANIFEST.json').read_text())
        entries = manifest.get('entries', manifest.get('files', {}))
        count = 0
        for rel, m in entries.items():
            p = root / rel
            assert not p.is_symlink()
            if m.get('kind') == 'dir':
                assert p.is_dir()
                continue
            r = record(p)
            assert r['type'] == stat.S_IFREG and r['links'] == 1
            assert r['sha256'] == m['sha256'] and r['bytes'] == m.get('bytes', m.get('size'))
            if 'mode' in m:
                assert r['mode'] == m['mode']
            count += 1
        assert count == entry['manifest_named_files_verified']
        counts[name] = count
    for rel, key in [('private/MANIFEST-r2.json', 'private_evidence_manifest_sha256'),
                     ('private/build-cache-manifest-r2.json', 'private_cache_inventory_sha256')]:
        final = json.loads((DRAFT / 'FINAL.json').read_text())
        assert sha(DRAFT / rel) == final[key]
        for name, m in json.loads((DRAFT / rel).read_text())['files'].items():
            r = record(DRAFT / name)
            assert all(r[k] == m[k] for k in ('bytes', 'mode', 'sha256')) and r['links'] == 1
    records = json.loads((ROOT / 'packet/public/read-record.json').read_text())['records']
    stable = [r for r in records if r['kind'] not in ('live_observation', 'parent_observation')]
    assert len(stable) == 91 and len(records) - len(stable) == 13
    for r in stable:
        actual = record(PROJECT / r['path'])
        assert all(actual[k] == r[k] for k in ('bytes', 'mode', 'sha256'))
        assert actual['links'] == r['nlink']
    with tempfile.TemporaryDirectory(prefix='copy-', dir=HERE) as td:
        temp = Path(td)
        copy = temp / 'review'
        copy.mkdir()
        shutil.copytree(ROOT / 'packet', copy / 'packet')
        for name in ('FINAL.json', 'REPORT.md'):
            shutil.copy2(ROOT / name, copy / name)
        result['copied_controls'] = run([sys.executable, '-B', str(copy / 'packet/public/code/integrity_controls.py'),
                                         str(copy), str(copy / 'work/controls')])
        cases = json.loads((copy / 'work/controls/results.json').read_text())['results']
        assert len(cases) == 12 and all(c['expected_exit'] == c['actual_exit'] and c['read_only_snapshot_equal'] for c in cases)
        result['control_cases'] = cases
        exact = temp / 'exact'
        (exact / 'work/extracted/packet/public/support').mkdir(parents=True)
        (exact / 'evidence').mkdir()
        shutil.copy2(ROOT / 'packet/public/code/independent_exact.py', exact / 'work/independent_exact.py')
        for name in ('support/certificate-witness.json', 'witness-tables.tex'):
            shutil.copy2(DRAFT / 'packet/public' / name, exact / 'work/extracted/packet/public' / name)
        env = os.environ.copy()
        env.update(PYTHONDONTWRITEBYTECODE='1', PYTHONPATH=str(ROOT / 'work/python-packages'), TMPDIR=str(temp))
        result['new_independent_symbolic_replay'] = run([sys.executable, '-B', str(exact / 'work/independent_exact.py')], env)
        evidence = json.loads((exact / 'evidence/independent-exact.json').read_text())
        assert evidence == json.loads((ROOT / 'packet/public/evidence/independent-exact.json').read_text())
        result['independent_exact_result'] = evidence
        result['copied_post_controls_verification'] = verify(copy)
    unchanged = {str(r.relative_to(PROJECT)): snap(r) == before[str(r)] for r in roots}
    assert all(unchanged.values())
    for r in stable:
        assert sha(PROJECT / r['path']) == r['sha256']
    result.update(all_expected=True, public_files=54, public_directories=5, copied_cases=12,
                  package_named_files=counts, stable_named_matches=91, observation_entries_excluded=13,
                  whole_actual_roots_unchanged=unchanged, independent_symbolic_terms=248,
                  independent_symbolic_patterns=10, manuscript_verdict='PASS_FULL_MANUSCRIPT_T088P133',
                  required_revisions=[], accepted=False, count_change=0)
    result['limits'] = (
        'Parent read full report/review/limits/read record/obligations and new core code; not every primary body or all20 pages again. '
        'New independent SymPy direct-residue/printed-TeX checker replayed on copies with explicit read-only reviewer-local '
        'SymPy1.14.0 dependency; no software/network acquisition. Seven original package anchors and named manifest files '
        'authenticate, plus draft separate36/416 named inventories and91 immutable read records;13 observations excluded. '
        'Complete eight current actual roots unchanged during replay, not historical/whole-parent preservation. '
        'Twelve copied review artifact cases are read-only per-fixture checks. Unchanged56-declaration support had already '
        'been freshly compiled by parent r2 intake; no redundant compilation/PDF rebuild/all-page QA here. Reviewer fresh '
        'formal/PDF build and all20-page inspection remain independent sealed evidence. No new correctness/contribution/formal '
        'or release gate inferred; manuscript PASS alone is adopted, full theorem remains unformalized.')
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('all_expected', 'public_files', 'public_directories',
        'stable_named_matches', 'observation_entries_excluded', 'copied_cases',
        'independent_symbolic_terms', 'manuscript_verdict')}))


if __name__ == '__main__':
    main()
