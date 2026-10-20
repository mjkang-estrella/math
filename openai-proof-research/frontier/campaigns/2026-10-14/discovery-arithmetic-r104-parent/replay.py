"""Parent PREFREEZE intake: artifact identities and finite GF(4) diagnostic."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[3]
ROOT = HERE.parent / 'fresh-arithmetic-discovery-r104'
ANCHORS = {'final': '72f9df00a996522345448392a3cf3e6043354c157d6e8c496dd9d08fda554472',
           'manifest': 'f48e5b35587c9b884a9e8c4d21cd429dfdf8a3e58509fc6a9bd8066920f17ed1',
           'report': 'edc6c2e25c0497986896c8ad0b186ab03c95a26ac013cdcb3c3b61d728c35cb6'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root):
    rows = {}
    for path in sorted(root.rglob('*')):
        info = path.lstat()
        row = {'mode': stat.S_IMODE(info.st_mode), 'links': info.st_nlink,
               'kind': 'directory' if path.is_dir() else 'file'}
        if path.is_symlink():
            row.update(kind='symlink', target=str(path.readlink()))
        elif path.is_file():
            row.update(size=info.st_size, sha256=sha(path))
        rows[str(path.relative_to(root))] = row
    return rows


def run(args):
    result = subprocess.run(args, capture_output=True, text=True, timeout=60,
                            env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    assert result.returncode == 0, result.stderr + result.stdout[:500]
    return result


def main():
    before = snapshot(ROOT)
    (HERE / 'observed-root.json').write_text(json.dumps(before, indent=2) + '\n')
    for key, rel in [('final', 'packet/FINAL.json'), ('manifest', 'packet/MANIFEST.json'), ('report', 'REPORT.md')]:
        assert sha(ROOT / rel) == ANCHORS[key]
    manifest = json.loads((ROOT / 'packet/MANIFEST.json').read_text())
    assert len(manifest['payloads']) == 93 and len(manifest['directories']) == 47
    for rel, row in manifest['payloads'].items():
        path = ROOT / 'packet' / rel
        assert sha(path) == row['sha256'] and path.stat().st_size == row['size']
        assert stat.S_IMODE(path.stat().st_mode) == row['mode'] and not path.is_symlink()
    args = sum((['--' + key + '-sha256', val] for key, val in ANCHORS.items()), [])
    result = run([sys.executable, '-B', str(ROOT / 'packet/public/verify.py'), '--root', str(ROOT),
                  *args, '--original-project', str(PROJECT)])
    verified = json.loads(result.stdout)
    assert (verified['payloads'], verified['directories'], verified['pinned_blobs'],
            verified['primary_pdfs'], verified['stable_originals_compared']) == (93, 47, 31, 6, 17)
    current = {}; stable = []; observations = []
    for category in ['context', 'history']:
        for row in json.loads((ROOT / ('packet/private/' + category + '/bindings.json')).read_text()):
            assert sha(ROOT / 'packet/private' / category / row['path']) == row['sha256']
            h = sha(PROJECT / row['path']); current[row['path']] = h
            if row['kind'] == 'stable_input':
                assert h == row['sha256']; stable.append(row['path'])
            else:
                observations.append({'path': row['path'], 'captured_sha256': row['sha256'],
                                     'current_sha256': h, 'currently_matches_capture': h == row['sha256']})
    assert len(current) == 20 and len(stable) == 17 and len(observations) == 3
    with tempfile.TemporaryDirectory(prefix='copied-', dir=HERE) as td:
        # The original controls script requires this basename; no source rewrite.
        copy = Path(td) / ROOT.name
        shutil.copytree(ROOT / 'packet', copy / 'packet')
        shutil.copy2(ROOT / 'REPORT.md', copy / 'REPORT.md')
        control_run = run([sys.executable, '-B', str(copy / 'packet/public/control_check.py'), *args])
        controls = json.loads(control_run.stdout)
        assert len(controls['cases']) == 10 and controls['all_controls_pass']
        assert all(c['expected_behavior'] and c['fixture_unchanged_by_verifier'] for c in controls['cases'])
        assert controls['original_sealed_packet_and_report_unchanged']
        (HERE / 'copied-controls.json').write_text(control_run.stdout)
        finite = run([sys.executable, '-B', str(copy / 'packet/public/growth_check.py')])
        diagnostic = json.loads(finite.stdout)
        assert len(diagnostic['cases']) == 4 and diagnostic['max_matrix_dimension'] == 162
        assert diagnostic == json.loads((ROOT / 'packet/public/growth_check.json').read_text())
        (HERE / 'growth-check.json').write_text(finite.stdout)
    assert snapshot(ROOT) == before
    assert all(sha(PROJECT / path) == h for path, h in current.items())
    record = {'observed_utc': datetime.now(timezone.utc).isoformat(), 'status': 'PREFREEZE_NO_NOMINEE_ARTIFACT_INTAKE',
              'all_expected': True, 'anchors': ANCHORS, 'payloads': 93, 'packet_files_including_seals': 95,
              'packet_directories': 47, 'pinned_blobs': 31, 'primary_pdf_receipts': 6,
              'stable_named_originals': stable, 'mutable_observations': observations,
              'whole_actual_author_root_unchanged': True, 'current_named_originals_unchanged': 20,
              'copied_artifact_cases': 10, 'negative_artifact_cases': 9, 'per_case_fixture_preservation': True,
              'finite_diagnostic_matches': True, 'GF4_cases': 4, 'max_matrix_dimension': 162,
              'full_global_upper_bound': 'UNPROVED_UNCHANGED', 'correctness': 'UNREVIEWED',
              'contribution': 'UNREVIEWED_AUTHOR_NONNOMINATION', 'accepted': False, 'count_change': 0,
              'campaign_count': 19, 'remaining': 1, 'publication': 'STOPPED',
              'limits': 'Parent read full report/derivation/readings/worklog/verifier/control/GF4 code,parsed metadata. '
              'Exact93payload+2sealfile/47directory inventory/modes andsingle-link regularfiles,31pinned blobs,6primaryPDF '
              'receipts and20retained bindings authenticate. Seventeen stable current originals match;three observations separate. '
              'Protected source/primary/history/search bodies are hash-authenticated,not semantic parent rereads. '
              'Ten copied artifact cases include9negative andper-case fixture byte/path/mode checks,but no hardlink-count '
              'snapshot/syscall denial. Complete current author root and20currentnamed originals stay unchanged;not historical '
              'whole-parent preservation. GF4fourcases/max162 reproduce,not the full gamma<=b comparison or a proof/contribution '
              'gate. Original controls basename guard is satisfied by fresh copy basename,no source edit. Source/primary '
              'partial/late reads,failedv3/Carlsonacquisition and search/corpus limits remain. No nominee/freeze/substitute.'}
    (HERE / 'replay.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({key: record[key] for key in ['all_expected', 'payloads', 'packet_directories', 'pinned_blobs',
                     'primary_pdf_receipts', 'copied_artifact_cases', 'GF4_cases', 'max_matrix_dimension', 'count_change']}))


if __name__ == '__main__':
    main()
