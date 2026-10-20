"""Parent artifact and finite-diagnostic intake; no mathematical review gate."""
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
ROOT = HERE.parent / 'fresh-arithmetic-discovery-r103'
ANCHORS = {'final': '58a6cfd87922fffda41ab5ba139b53421e77cc87f02c13189d8da7f2266b068b',
           'manifest': 'eaa742685df86997ac36dce017b15514b429b2e442bf7b0ff22bd058bed1f563',
           'report': '673e677af56cb4908077f9fa6a47d537b38182b04f638a47f47ef5c1694e1791'}
NAMES = {'final': 'packet/FINAL.json', 'manifest': 'packet/MANIFEST.json', 'report': 'REPORT.md'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root):
    result = {}
    for path in sorted(root.rglob('*')):
        s = path.lstat()
        item = {'mode': stat.S_IMODE(s.st_mode), 'links': s.st_nlink,
                'kind': 'directory' if path.is_dir() else 'file'}
        if path.is_symlink():
            item.update(kind='symlink', target=str(path.readlink()))
        elif path.is_file():
            item.update(bytes=s.st_size, sha256=sha(path))
        result[str(path.relative_to(root))] = item
    return result


def run(argv, cwd=None):
    result = subprocess.run(argv, cwd=cwd, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'},
                            text=True, capture_output=True, timeout=60)
    assert result.returncode == 0, result.stderr
    return result


def main():
    before = snapshot(ROOT)
    (HERE / 'observed-root.json').write_text(json.dumps(before, indent=2) + '\n')
    for key, rel in NAMES.items():
        assert sha(ROOT / rel) == ANCHORS[key]
    manifest = json.loads((ROOT / NAMES['manifest']).read_text())
    files = manifest['files']
    assert len(files) == 64 and len(manifest['directories']) == 35
    actual = {str(p.relative_to(ROOT / 'packet')) for p in (ROOT / 'packet').rglob('*') if p.is_file()}
    assert actual == set(files) | {'MANIFEST.json'}
    for rel, rec in files.items():
        p = ROOT / 'packet' / rel
        assert sha(p) == rec['sha256'] and p.stat().st_size == rec['bytes'] and not p.is_symlink()
    args = sum((['--' + k + '-sha256', v] for k, v in ANCHORS.items()), [])
    verification = run([sys.executable, '-B', str(ROOT / 'packet/public/verify.py'), str(ROOT), *args])
    verified = json.loads(verification.stdout)
    assert verified['payload_files'] == 64 and verified['pinned_blobs'] == 19 and verified['directories'] == 35
    stable = []; observations = []; current = {}
    for category in ['context', 'history']:
        rows = json.loads((ROOT / ('packet/private/' + category + '/bindings.json')).read_text())
        for rec in rows:
            assert sha(ROOT / 'packet/private' / category / rec['path']) == rec['sha256']
            h = sha(PROJECT / rec['path']); current[rec['path']] = h
            if rec.get('mutable', False):
                observations.append({'path': rec['path'], 'archival_sha256': rec['sha256'],
                                     'current_sha256': h, 'currently_matches_archive': h == rec['sha256']})
            else:
                assert h == rec['sha256']
                stable.append(rec['path'])
    assert len(stable) == 10 and len(observations) == 3 and len(current) == 13
    primary = json.loads((ROOT / 'packet/private/primary/acquisition.json').read_text())
    assert len(primary) == 3
    for rec in primary:
        matching = [rel for rel, m in files.items() if m['sha256'] == rec['sha256']]
        assert len(matching) == 1 and (ROOT / 'packet' / matching[0]).stat().st_size == rec['bytes']
    with tempfile.TemporaryDirectory(prefix='copied-', dir=HERE) as td:
        copied = Path(td) / 'root'
        shutil.copytree(ROOT / 'packet', copied / 'packet')
        shutil.copy2(ROOT / 'REPORT.md', copied / 'REPORT.md')
        controls = run([sys.executable, '-B', str(copied / 'packet/public/control_check.py'), str(copied), *args])
        control_data = json.loads(controls.stdout)
        assert len(control_data['controls']) == 7 and control_data['sealed_packet_and_report_unchanged']
        assert all(c['read_only_observed'] and ((c['returncode'] == 0) == c['expected_success'])
                   for c in control_data['controls'])
        (HERE / 'controls.json').write_text(controls.stdout)
        seed = run([sys.executable, '-B', str(copied / 'packet/public/seed_check.py')], cwd=td)
        assert json.loads(seed.stdout) == json.loads((ROOT / 'packet/public/seed-check.json').read_text())
        (HERE / 'seed-check.json').write_text(seed.stdout)
    assert snapshot(ROOT) == before
    assert all(sha(PROJECT / rel) == h for rel, h in current.items())
    result = {'observed_utc': datetime.now(timezone.utc).isoformat(),
              'status': 'PREFREEZE_NO_NOMINEE_ARTIFACT_INTAKE', 'anchors': ANCHORS,
              'all_expected': True, 'payload_files': 64, 'packet_directories': 35,
              'canonical_pinned_blobs': 19, 'primary_pdf_hashes_authenticated': 3,
              'stable_named_originals': stable, 'mutable_observations': observations,
              'current_named_originals_unchanged': 13, 'copied_artifact_controls': 7,
              'seed_diagnostic_matches': True, 'whole_actual_root_unchanged': True,
              'original_root_entries': len(before), 'accepted': False, 'count_change': 0,
              'campaign_count': 19, 'remaining': 1, 'publication': 'STOPPED',
              'correctness_review': 'NOT_PERFORMED', 'contribution_review': 'NOT_PERFORMED',
              'limits': 'Parent read full report/derivation/readings/worklog/verifier/control/seed code and parsed bindings/acquisitions. '
              'Private source/primary/history/search bodies authenticated,not semantically reread by parent. '
              'External anchors bootstrap exact64-payload35-directory packet and19pinned blobs. Seven copied controls '
              'observe per-fixture bytes/directory preservation but not modes/hardlinks/syscall denial;original verifier '
              'does not authenticate modes/hardlink counts. Complete current actual root and13current named originals '
              'remain unchanged during replay,not historical whole-parent preservation. Ten stable inputs match;three '
              'mutable copies are separate observations. Fresh rational seed diagnostic is finite support,not generic '
              'division/infinite construction proof,independent mathematical verdict or worldwide novelty clearance.'}
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'all_expected', 'payload_files', 'packet_directories',
                     'canonical_pinned_blobs', 'copied_artifact_controls', 'whole_actual_root_unchanged', 'count_change']}))


if __name__ == '__main__':
    main()
