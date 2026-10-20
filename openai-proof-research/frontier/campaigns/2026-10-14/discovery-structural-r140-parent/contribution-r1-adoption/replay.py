"""Authenticate/adopt a contribution packet; no full correctness verdict."""
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
PROJECT = HERE.parents[4]
BASE = PROJECT / 'frontier/campaigns/2026-10-14'
ROOT = BASE / 't205q140-contribution-r1'
ANCHORS = {'MANIFEST.json': 'de7d844f0f3c3783ebad4586175b7f7f5f53a3626ea18dd5f76bc527af5d2d5c',
           'outsideREPORT.md': 'd40cd1baf766137ac78e2dc629edbe5cb5d3e8cad2f4b6fc73e03945055d7aff',
           'FINAL.json': 'b713f9096e733a830cde65854c0a419d0a1eb122a77f75063a4b2fdc387cad0f',
           'controls/receipt.json': 'd4f81a3d071c223176e29db452f8fa550c1437f2ca17bfd817b8abf6c96ccc2c',
           'controls/preservation-after.json': '9638b839df1ed86abac9ff81e7b463edb81a5819203da5b5687dd8204b34807f',
           'packet/public/review.md': '66fb8c7e0fa78c1f6604632433b07295b1630f6ed034115c4c9b8a134e356968',
           'ANCHORS.json': '75e5f14eb819573d8f5305ed9541f7ecd5a54ca2a6263cf2d040cbdf93e96dcb'}


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


def original_baseline():
    rows = {}
    for name in ['fresh-structural-discovery-r139', 'fresh-structural-discovery-r140']:
        root = BASE / name
        for path in [root, *root.rglob('*')]:
            info = path.lstat()
            assert not path.is_symlink()
            rows[str(path.relative_to(PROJECT))] = {
                'kind': 'file' if path.is_file() else 'directory',
                'mode': stat.S_IMODE(info.st_mode), 'nlink': info.st_nlink,
                **({'sha256': sha(path), 'size': info.st_size} if path.is_file() else {})}
    return rows


def command(root, manifest_hash=None):
    return [sys.executable, '-B', str(root / 'packet/public/verify.py'), '--root', str(root),
            '--manifest-sha256', manifest_hash or ANCHORS['MANIFEST.json'],
            '--report-sha256', ANCHORS['outsideREPORT.md'], '--final-sha256', ANCHORS['FINAL.json']]


def verify(args, expected):
    result = subprocess.run(args, capture_output=True, text=True, timeout=30,
                            env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    assert (result.returncode == 0) == expected, result.stdout + result.stderr
    return {'returncode': result.returncode, 'stdout': result.stdout.strip(), 'stderr': result.stderr.strip()}


def main():
    review_before = snapshot(ROOT); originals_before = original_baseline()
    (HERE / 'observed-roots.json').write_text(json.dumps({'review': review_before, 'originals': originals_before}, indent=2) + '\n')
    for rel, h in ANCHORS.items():
        assert sha(ROOT / rel) == h and not (ROOT / rel).is_symlink()
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert len(manifest['entries']) == 123
    for row in manifest['entries']:
        path = ROOT / row['path']
        if row['kind'] == 'file':
            assert sha(path) == row['sha256'] and path.stat().st_size == row['size']
    assert sum(x['kind'] == 'file' for x in manifest['entries']) == 94
    original_verification = verify(command(ROOT), True)
    assert json.loads(original_verification['stdout'])['pinned_blobs'] == 18
    assert originals_before == json.loads((ROOT / 'packet/private/originals-before.json').read_text())
    assert len(originals_before) == 306
    bindings = json.loads((ROOT / 'packet/private/input-bindings.json').read_text())
    current = {}
    for row in bindings:
        assert sha(ROOT / row['copy']) == row['sha256']
        current[row['original']] = sha(PROJECT / row['original'])
        assert current[row['original']] == row['sha256']
    assert len(bindings) == len(current) == 57
    controls = []
    with tempfile.TemporaryDirectory(prefix='fixtures-', dir=HERE) as td:
        copy = Path(td) / 'review'
        for name in ['packet', 'work']:
            shutil.copytree(ROOT / name, copy / name)
        for name in ['MANIFEST.json', 'outsideREPORT.md', 'FINAL.json']:
            shutil.copy2(ROOT / name, copy / name)
        verify(command(copy), True)
        initial_copy = snapshot(copy)
        proof = copy / 'packet/public/review.md'; original = proof.read_bytes()

        def test(label, change, restore, wrong_anchor=False):
            try:
                change(); before = snapshot(copy)
                result = verify(command(copy, '0' * 64) if wrong_anchor else command(copy), False)
                assert snapshot(copy) == before
                controls.append({'case': label, 'rejected': True, 'fixture_unchanged_by_verifier': True, **result})
            finally:
                restore()
        test('changed_review', lambda: proof.write_bytes(original + b'\nmutation\n'), lambda: proof.write_bytes(original))
        test('missing_review', proof.unlink, lambda: proof.write_bytes(original))
        extra = copy / 'packet/public/unlisted'
        test('extra_payload', lambda: extra.write_text('fixture'), extra.unlink)
        link = copy / 'packet/public/link'
        test('payload_symlink', lambda: link.symlink_to('review.md'), link.unlink)
        for name in ['MANIFEST.json', 'outsideREPORT.md', 'FINAL.json']:
            path = copy / name; data = path.read_bytes()
            test('changed_' + name, lambda p=path, b=data: p.write_bytes(b + b' '),
                 lambda p=path, b=data: p.write_bytes(b))
        test('wrong_external_anchor', lambda: None, lambda: None, True)
        mp = copy / 'MANIFEST.json'; fp = copy / 'FINAL.json'
        mb = mp.read_bytes(); fb = fp.read_bytes()

        def forge():
            proof.write_bytes(original + b'\nforged\n'); m = json.loads(mb)
            row = next(x for x in m['entries'] if x['path'] == 'packet/public/review.md')
            row.update(size=proof.stat().st_size, sha256=sha(proof))
            mp.write_text(json.dumps(m, indent=2) + '\n')
            f = json.loads(fb); f.update(manifest_sha256=sha(mp), review_sha256=sha(proof))
            fp.write_text(json.dumps(f, indent=2) + '\n')

        def restore():
            proof.write_bytes(original); mp.write_bytes(mb); fp.write_bytes(fb)
        test('coherent_local_reseal_against_old_external_anchors', forge, restore)
        verify(command(copy), True); assert snapshot(copy) == initial_copy
    assert len(controls) == 9
    (HERE / 'copied-controls.json').write_text(json.dumps(controls, indent=2) + '\n')
    assert snapshot(ROOT) == review_before and original_baseline() == originals_before
    assert all(sha(PROJECT / path) == h for path, h in current.items())
    result = {'observed_utc': datetime.now(timezone.utc).isoformat(), 'candidate': 'T205Q140',
              'status': 'CONTRIBUTION_PACKET_AUTHENTICATED_PARENT_REPLAY', 'all_expected': True,
              'anchors': ANCHORS, 'payload_entries': 123, 'payload_files': 94, 'payload_directories': 29,
              'pinned_blobs': 18, 'retained_primary_pairs': 5, 'new_primary_pairs': 6,
              'named_copies_and_current_originals_match': 57, 'original_r139_r140_entries': 306,
              'whole_actual_review_and_original_roots_unchanged': True,
              'copied_negative_controls': 9, 'per_fixture_verifier_preservation': True,
              'correctness_gate': 'NOT_PERFORMED', 'accepted': False, 'count_change': 0,
              'campaign_count': 19, 'remaining': 1, 'publication': 'STOPPED',
              'limits': 'Parent read full report/review/readlimits/notes/verifier/controls and parsed receipts/bindings. '
              'Review full text recovered after truncated combined display. The constructive uniform-minimum/profile-factorial '
              'argument is checked against primary bounds read at prior author intake;new older primary/source/history bodies '
              'not fully reread by parent. Seven external anchors,123entry94file29directory packet/work,18pinned blobs, '
              '11primaryPDF/textpairs and57namedcurrent originals authenticate;historical/mutable categories retained. '
              'Complete current reviewroot and306entryr139/r140baseline unchanged,not historicalwholeparent preservation. '
              'Child verifier omits modes/hardlink contract;current parent snapshots are separate. Original copied_controls.py '
              'depends on original sibling/layout baseline and was read,not run from a fabricated portable copy. Parent own '
              'nine copied controls use externally anchored verifier,check per-fixture preservation and restore exact bytes. '
              'No redundant finite-character replay or independent full correctness/novelty verdict. No source/math repair.'}
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['all_expected', 'payload_entries', 'payload_files', 'pinned_blobs',
                     'named_copies_and_current_originals_match', 'copied_negative_controls', 'count_change']}))


if __name__ == '__main__':
    main()
