"""Recover unsealed interrupted work; this is not a child seal or a proof review."""
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
ROOT = HERE.parent / 'fresh-structural-discovery-r139'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root):
    result = {}
    for path in sorted(root.rglob('*')):
        info = path.lstat()
        item = {'mode': stat.S_IMODE(info.st_mode), 'links': info.st_nlink,
                'kind': 'directory' if path.is_dir() else 'file'}
        if path.is_symlink():
            item.update(kind='symlink', target=str(path.readlink()))
        elif path.is_file():
            item.update(bytes=info.st_size, sha256=sha(path))
        result[str(path.relative_to(root))] = item
    return result


def main():
    baseline = json.loads((HERE / 'observed-root.json').read_text())['entries']
    assert snapshot(ROOT) == baseline
    assert len(baseline) == 83 and sum(x['kind'] == 'file' for x in baseline.values()) == 64
    assert not any((ROOT / x).exists() for x in ['FINAL.json', 'REPORT.md', 'packet/MANIFEST.json'])
    tree_file = PROJECT / 'sources/preprints-tree.json'
    assert sha(tree_file) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_file.read_text())
    assert not tree['truncated'] and len(tree['tree']) == 13223
    entries = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'packet/private/controls/source-receipts.json').read_text())
    assert len(sources) == 20
    for rec in sources:
        data = (ROOT / 'packet/private/sources' / rec['path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert blob == entries[rec['path']]['sha'] == rec['git_blob']
        assert len(data) == entries[rec['path']]['size'] == rec['size']
        assert hashlib.sha256(data).hexdigest() == rec['sha256']
    primaries = json.loads((ROOT / 'packet/private/controls/primary-receipts.json').read_text())
    assert len(primaries) == 3
    for rec in primaries:
        pdf = ROOT / 'packet/private/primary' / (rec['name'] + '.pdf')
        text = pdf.with_suffix('.txt')
        assert sha(pdf) == rec['sha256'] and pdf.stat().st_size == rec['bytes']
        assert sha(text) == rec['text_sha256']
    bindings = json.loads((ROOT / 'packet/private/controls/bindings.json').read_text())
    assert len(bindings) == 17
    stable = []; observations = []; current_before = {}
    for rec in bindings:
        assert sha(ROOT / rec['copy']) == rec['sha256']
        path = PROJECT / rec['original']
        current_before[rec['original']] = sha(path)
        if rec['stable']:
            assert current_before[rec['original']] == rec['sha256']
            stable.append(rec['original'])
        else:
            observations.append({'original': rec['original'], 'current_sha256': current_before[rec['original']],
                                 'archival_sha256': rec['sha256'],
                                 'currently_matches_archive': current_before[rec['original']] == rec['sha256']})
    # The unsealed script was fully read by the parent. Its current bytes are
    # bound by our post-failure snapshot, not a nonexistent child detached seal.
    original_script = ROOT / 'packet/public/checks.py'
    with tempfile.TemporaryDirectory(prefix='diagnostic-', dir=HERE) as td:
        copied = Path(td) / 'checks.py'
        shutil.copy2(original_script, copied)
        assert sha(copied) == baseline['packet/public/checks.py']['sha256']
        run = subprocess.run([sys.executable, '-B', str(copied)], cwd=td,
                             env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'},
                             text=True, capture_output=True, timeout=60)
        assert run.returncode == 0, run.stderr
        assert json.loads(run.stdout) == json.loads((ROOT / 'packet/public/checks-receipt.json').read_text())
        assert sha(copied) == baseline['packet/public/checks.py']['sha256']
        (HERE / 'diagnostic-output.json').write_text(run.stdout)
        (HERE / 'diagnostic-stderr.txt').write_text(run.stderr)
    assert snapshot(ROOT) == baseline
    assert all(sha(PROJECT / p) == h for p, h in current_before.items())
    result = {'observed_utc': datetime.now(timezone.utc).isoformat(),
              'status': 'UNSEALED_PARTIAL_SUPPORT_RECOVERED_AFTER_PROVIDER_CAPACITY_FAILURE',
              'all_expected': True, 'original_entries': 83, 'original_files': 64,
              'canonical_source_bodies': 20, 'primary_pdf_and_text_pairs': 3,
              'stable_named_bindings': stable, 'mutable_archival_observations': observations,
              'finite_diagnostics_match': True,
              'diagnostic_output_sha256': sha(HERE / 'diagnostic-output.json'),
              'actual_original_root_unchanged': True, 'current_named_originals_unchanged': 17,
              'detached_child_seal_available': False,
              'full_theorem_nominee': False, 'correctness_review': 'NOT_PERFORMED',
              'contribution_review': 'NOT_PERFORMED', 'accepted': False, 'count_change': 0,
              'campaign_count': 19, 'remaining': 1, 'publication': 'STOPPED',
              'limits': 'Parent read all durable public derivations/notes/check code and parsed receipts/bindings. '
              'Source and primary checks authenticate retained bytes,not semantic parent reads of those bodies. '
              'Current post-failure83-entry/64-file snapshot and17 named originals stay unchanged during replay; '
              'not a prior child seal,historical preservation,syscall sandbox,full math review or novelty audit. '
              'No child FINAL/MANIFEST/outsideREPORT/read-only artifact verifier/control suite was completed. '
              'Finite exact script runs on a fresh copy and matches its saved diagnostic;not an integrity-mutation suite '
              'or proof of the unpaid full connected mixing bound. Historical mutable campaign copy differs as expected.'}
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'all_expected', 'original_files',
                     'canonical_source_bodies', 'primary_pdf_and_text_pairs', 'finite_diagnostics_match',
                     'actual_original_root_unchanged', 'count_change']}))


if __name__ == '__main__':
    main()
