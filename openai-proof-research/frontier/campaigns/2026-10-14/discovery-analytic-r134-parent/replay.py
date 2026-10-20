"""Parent K369R134 artifact/finite intake, without a mathematical verdict."""
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
ROOT = HERE.parent / 'fresh-analytic-discovery-r134'
ANCHORS = {'FINAL.json': '5d5d8331ff31c815295b79014aeb243f7a9ca42d3188a7f35c58952f91d0eaac',
           'MANIFEST.json': 'ad053e6a69d9b0727249f444d761740c4c490c4f3c2391676f03ae053aecaee6',
           'REPORT.md': '0e9ea3fb45821091dacc3e0c5c1744f79ad00a36408fcce564943076b5c4806f'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root):
    rows = {}
    for path in sorted(root.rglob('*')):
        s = path.lstat()
        row = {'mode': stat.S_IMODE(s.st_mode), 'links': s.st_nlink,
               'kind': 'directory' if path.is_dir() else 'file'}
        if path.is_symlink():
            row.update(kind='symlink', target=str(path.readlink()))
        elif path.is_file():
            row.update(bytes=s.st_size, sha256=sha(path))
        rows[str(path.relative_to(root))] = row
    return rows


def invoke(args):
    result = subprocess.run(args, capture_output=True, text=True, timeout=60,
                            env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    assert result.returncode == 0, result.stderr
    return result


def main():
    before = snapshot(ROOT)
    (HERE / 'observed-root.json').write_text(json.dumps(before, indent=2) + '\n')
    for name, h in ANCHORS.items():
        assert sha(ROOT / name) == h
    final = json.loads((ROOT / 'FINAL.json').read_text())
    assert sha(ROOT / 'verify.py') == final['verifier_sha256']
    records = json.loads((ROOT / 'MANIFEST.json').read_text())['files']
    assert len(records) == 39
    for row in records:
        path = ROOT / row['path']
        assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes'] and not path.is_symlink()
    args = ['--final-sha256', ANCHORS['FINAL.json'], '--manifest-sha256', ANCHORS['MANIFEST.json'],
            '--report-sha256', ANCHORS['REPORT.md']]
    verified = invoke([sys.executable, '-B', str(ROOT / 'verify.py'), '--root', str(ROOT), *args])
    assert json.loads(verified.stdout)['files'] == 39
    treefile = PROJECT / 'sources/preprints-tree.json'
    assert sha(treefile) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(treefile.read_text()); assert len(tree['tree']) == 13223 and not tree['truncated']
    bypath = {x['path']: x for x in tree['tree']}
    sources = json.loads((ROOT / 'packet/private/source-acquisition.json').read_text())
    assert len(sources) == 10
    for row in sources:
        data = (ROOT / 'packet/private/source' / Path(row['local']).name).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert len(data) == row['size'] == bypath[row['path']]['size']
        assert blob == row['sha'] == bypath[row['path']]['sha']
        assert hashlib.sha256(data).hexdigest() == row['sha256']
    primary = json.loads((ROOT / 'packet/private/primary/acquisition.json').read_text())
    assert len(primary) == 2
    for row in primary:
        assert sha(ROOT / 'packet/private/primary' / (row['name'] + '.pdf')) == row['sha256']
    current = {}; stable = []; observations = []
    for row in json.loads((ROOT / 'packet/private/late-bindings.json').read_text()):
        assert sha(ROOT / row['copy']) == row['sha256']
        h = sha(Path(row['original_path'])); current[row['original_path']] = h
        if row['mutable_observation']:
            observations.append({'path': row['original_path'], 'captured_sha256': row['sha256'],
                                 'current_sha256': h, 'currently_matches_capture': h == row['sha256']})
        else:
            assert h == row['sha256']; stable.append(row['original_path'])
    assert len(current) == 7 and len(stable) == 6 and len(observations) == 1
    # The outside controls script and postseal receipts lack an external handoff
    # hash binding. Record current hashes; execute only the fully read script on
    # copies, after the three-anchor verifier bootstrap above.
    observed_outside = {name: sha(ROOT / name) for name in ['artifact_controls.py', 'ANCHORS.json',
                        'ARTIFACT-BUILD-HISTORY.json', 'INTEGRITY-CONTROLS.json', 'ORIGINAL-PRESERVATION.json']}
    with tempfile.TemporaryDirectory(prefix='copied-', dir=HERE) as td:
        copied = Path(td) / 'root'
        shutil.copytree(ROOT / 'packet', copied / 'packet')
        for name in ['FINAL.json', 'MANIFEST.json', 'REPORT.md', 'verify.py', 'artifact_controls.py']:
            shutil.copy2(ROOT / name, copied / name)
        assert all(sha(copied / name) == h for name, h in ANCHORS.items())
        control_run = invoke([sys.executable, '-B', str(copied / 'artifact_controls.py')])
        controls = json.loads((copied / 'INTEGRITY-CONTROLS.json').read_text())
        assert len(controls['checks']) == 9 and all(x['control_pass'] for x in controls['checks'])
        assert sum(not x['expected_pass'] for x in controls['checks']) == 6
        assert controls['originals_unchanged'] and controls['copy_removed']
        (HERE / 'copied-controls.json').write_text(json.dumps(controls, indent=2) + '\n')
        (HERE / 'copied-preservation.json').write_text((copied / 'ORIGINAL-PRESERVATION.json').read_text())
        finite = invoke([sys.executable, '-B', str(copied / 'packet/public/check_math.py')])
        diagnostic = json.loads(finite.stdout)
        assert diagnostic['count'] == 177
        assert diagnostic == json.loads((ROOT / 'packet/public/math-check-result.json').read_text())
        (HERE / 'math-check.json').write_text(finite.stdout)
    assert snapshot(ROOT) == before
    assert all(sha(Path(path)) == h for path, h in current.items())
    result = {'observed_utc': datetime.now(timezone.utc).isoformat(), 'candidate': 'K369R134',
              'status': 'FULL_AUTHOR_PROOF_NOMINEE_ARTIFACT_INTAKE_ONLY', 'all_expected': True,
              'external_anchors': ANCHORS, 'packet_files': 39, 'pinned_source_blobs': 10,
              'primary_pdf_hashes': 2, 'stable_late_bindings': stable, 'mutable_observations': observations,
              'current_named_originals_unchanged': 7, 'whole_actual_author_root_unchanged': True,
              'observed_outside_seal_sha256': observed_outside, 'artifact_cases': 9,
              'negative_artifact_cases': 6, 'exact_support_checks': 177,
              'scope_sha256': final['frozen_scope_sha256'], 'proof_sha256': sha(ROOT / 'packet/public/author-proof.md'),
              'correctness': 'UNREVIEWED', 'contribution': 'UNREVIEWED', 'accepted': False,
              'count_change': 0, 'campaign_count': 19, 'remaining': 1, 'publication': 'STOPPED',
              'limits': 'Parent read full scope/proof/prefreeze/provenance/report and verifier/control/math code. '
              'Targeted source04 kernel construction/estimate proof and05 theorem/context,Rozenblum radial formula; '
              'not all source/primary/history bodies. Three external handoff anchors bind39packet files and FINAL-bound '
              'verifier. Verifier does not authenticate exact empty-directory sets,modes,hardlinks,source Gitblobs or '
              'primary/binding originals;parent separately authenticates10sourceblobs,2PDFs and7latebindings. Six stable '
              'originals match;ledger is mutable. Outside controls/script/receipt/ANCHORS/build-history hashes are current '
              'parent observations,not externally authenticated child seals. Fully read controls script runs only on copies; '
              '9cases include6negative,not9rejections. Restored-input preservation,not per-case preservation/syscall denial. '
              'Whole actual author root and7currentnamed originals unchanged during replay,not historicalwholeparent '
              'preservation.177exactsupport checks reproduce,not all-frequency analytic correctness/substantiality. '
              'Provisional manifest ordering repair occurred before final handoff,with payload/frozen scope unchanged; '
              'late captures/search-pruning/incidental copied-review limitations remain. No original math/artifact repair.'}
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['candidate', 'all_expected', 'packet_files', 'pinned_source_blobs',
                     'primary_pdf_hashes', 'artifact_cases', 'negative_artifact_cases', 'exact_support_checks', 'count_change']}))


if __name__ == '__main__':
    main()
