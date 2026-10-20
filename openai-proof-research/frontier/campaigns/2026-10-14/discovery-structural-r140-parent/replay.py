"""Parent T205Q140 artifact intake, not a mathematical/contribution verdict."""
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
ROOT = HERE.parent / 'fresh-structural-discovery-r140'
OLD = HERE.parent / 'fresh-structural-discovery-r139'
ANCHORS = {'MANIFEST.json': '1753a005cba348729322bf80311b631ce710d13e601eb8fbcab4d3d228c5db5d',
           'outsideREPORT.md': 'ea36dd06172fb88cfb2d99f9d405b793dd08ff8e5bc2e1e57d839e8be3117a9a',
           'FINAL.json': 'f57424bd710b13f1f12063bf5f367d861cac5832991c64da4cd11efe08a86ad2',
           'packet/public/frozen-scope.md': '0b57f7972d43586f721a6e1aaa42cdd6fa8c80512702f933796b82e2bcd3f6ef',
           'controls/receipt.json': '54d15ff468b7df67402523b869aedaa319606a928d396dd863e15341e729666c',
           'controls/preservation-after.json': '21f0b32bb96817de931fb1dc53543687ee074c4d6480617b75c72777b5e37398',
           'ANCHORS.json': '42115cf1f83a59f0f9fe48d02ba6ca0be817fcaa054ec1dcbded6f77558d2973'}


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


def invoke(argv):
    result = subprocess.run(argv, capture_output=True, text=True, timeout=60,
                            env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    assert result.returncode == 0, result.stderr
    return result


def main():
    before = snapshot(ROOT); old_before = snapshot(OLD)
    (HERE / 'observed-roots.json').write_text(json.dumps({'r140': before, 'r139': old_before}, indent=2) + '\n')
    for rel, h in ANCHORS.items():
        assert sha(ROOT / rel) == h and not (ROOT / rel).is_symlink()
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    entries = manifest['entries']; assert len(entries) == 105
    for row in entries:
        path = ROOT / row['path']
        assert not path.is_symlink()
        if row['kind'] == 'file':
            assert sha(path) == row['sha256'] and path.stat().st_size == row['size']
        else:
            assert path.is_dir()
    assert sum(r['kind'] == 'file' for r in entries) == 76
    args = ['--manifest-sha256', ANCHORS['MANIFEST.json'], '--report-sha256', ANCHORS['outsideREPORT.md'],
            '--final-sha256', ANCHORS['FINAL.json']]
    verified = invoke([sys.executable, '-B', str(ROOT / 'packet/public/verify.py'), '--root', str(ROOT), *args])
    v = json.loads(verified.stdout)
    assert (v['payload_entries'], v['payload_files'], v['pinned_sources'], v['primary_pairs']) == (105, 76, 18, 5)
    current = {}; stable = []; observations = []
    for category in ['context', 'history']:
        rows = json.loads((ROOT / ('packet/private/' + category + '/bindings.json')).read_text())
        for row in rows:
            assert sha(ROOT / 'packet/private' / category / row['path']) == row['sha256']
            h = sha(PROJECT / row['path']); current[row['path']] = h
            mutable = row.get('mutable_observation', row['path'].startswith('frontier/findings/'))
            if mutable:
                observations.append({'path': row['path'], 'bound_sha256': row['sha256'], 'current_sha256': h,
                                     'currently_matches_binding': h == row['sha256']})
            else:
                assert h == row['sha256']; stable.append(row['path'])
    assert len(current) == 15 and len(stable) == 10 and len(observations) == 5
    old_baseline = json.loads((ROOT / 'packet/private/context/r139-initial-inventory.json').read_text())['entries']
    old_actual = [{'path': path, 'kind': row['kind'],
                   **({} if row['kind'] == 'directory' else {'size': row['size'], 'sha256': row['sha256']})}
                  for path, row in old_before.items()]
    assert old_actual == old_baseline and len(old_actual) == 83
    with tempfile.TemporaryDirectory(prefix='copied-', dir=HERE) as td:
        copy = Path(td) / 'root'
        for name in ['packet', 'work']:
            shutil.copytree(ROOT / name, copy / name)
        for name in ['MANIFEST.json', 'outsideREPORT.md', 'FINAL.json']:
            shutil.copy2(ROOT / name, copy / name)
        assert all(sha(copy / name) == ANCHORS[name] for name in ['MANIFEST.json', 'outsideREPORT.md', 'FINAL.json'])
        controls = invoke([sys.executable, '-B', str(copy / 'work/run_controls.py')])
        rec = json.loads((copy / 'controls/receipt.json').read_text())
        assert len(rec['mutation_controls']) == 9 and all(x['rejected'] for x in rec['mutation_controls'])
        assert rec['finite_diagnostic_replay_equal']
        assert rec['detached_original_anchors'] == {k: ANCHORS[k] for k in ['MANIFEST.json', 'outsideREPORT.md', 'FINAL.json']}
        (HERE / 'copied-controls.json').write_text(json.dumps(rec, indent=2) + '\n')
        finite = invoke([sys.executable, '-B', str(copy / 'packet/public/finite_check.py')])
        diagnostic = json.loads(finite.stdout)
        assert diagnostic == json.loads((ROOT / 'packet/private/finite-check.json').read_text())
        assert len(diagnostic['rows']) == 5 and sum(x['classes'] for x in diagnostic['rows']) == 1024
        (HERE / 'finite-check.json').write_text(finite.stdout)
    assert snapshot(ROOT) == before and snapshot(OLD) == old_before
    assert all(sha(PROJECT / path) == h for path, h in current.items())
    result = {'observed_utc': datetime.now(timezone.utc).isoformat(),
              'status': 'FULL_AUTHOR_PROOF_NOMINEE_ARTIFACT_INTAKE_ONLY', 'candidate': 'T205Q140',
              'anchors': ANCHORS, 'all_expected': True, 'payload_entries': 105, 'payload_files': 76,
              'payload_directories': 29, 'pinned_source_blobs': 18, 'primary_pdf_text_pairs': 5,
              'stable_named_originals': stable, 'mutable_observations': observations,
              'current_named_originals_unchanged': 15, 'r139_original_baseline_matches': True,
              'whole_actual_r139_and_r140_roots_unchanged': True, 'negative_controls': 9,
              'finite_diagnostic_matches': True, 'finite_classes': 1024,
              'correctness': 'UNREVIEWED', 'contribution': 'UNREVIEWED', 'accepted': False,
              'count_change': 0, 'campaign_count': 19, 'remaining': 1, 'publication': 'STOPPED',
              'limits': 'Parent read full frozen scope,author proof,working notes,read limits,README,rights,report,core verifier/finite/control/preservation code. '
              'Targeted primary reads confirm Teyssier Thm1.2,FS Thm1,Fulman Thm3.14 and proof;not full primary/history/source-body rereading. '
              'Exact105entry76file29directory packet/work authentication,18pinned blobs,5primaryPDF/text pairs and15namedcopies. '
              'Ten stable originals match;five observations separate. Whole current r139/r140 roots and15current named originals '
              'unchanged during replay,not historical whole-parent preservation. Nine copied tampering cases check rejection and '
              'restored fixture;original runner has no per-case preservation or modes/hardlink contract. Parent root snapshots '
              'include modes/link counts,not syscall denial. Finite m2..6 rows/m2..5 distributions reproduce;not the uniform tail,CLT, '
              'independent mathematical verdict or novelty audit. Acquisition statuses record initial not-yet-read state;later '
              'read limits/notes distinguish actual reads. No frozen-byte repair or count change.'}
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['candidate', 'all_expected', 'payload_entries', 'payload_files',
                     'pinned_source_blobs', 'primary_pdf_text_pairs', 'negative_controls', 'finite_classes', 'count_change']}))


if __name__ == '__main__':
    main()
