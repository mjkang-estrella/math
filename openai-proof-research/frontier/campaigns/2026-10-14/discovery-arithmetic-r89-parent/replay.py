#!/usr/bin/env python3
"""Parent authentication and immutable-input instrumentation of the same 16 controls."""
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
AUTHOR = HERE.parent / 'fresh-arithmetic-discovery-r89'
FINAL = '4e58ca2760db8c4a7aaa0415cddd33eefc1fc5d4e6dbcc4428f8d4d1d258f05a'
REPORT = 'a62dce3f36ac7cbc2e71af1393c16e54537e732037685be325fd263371eba9fa'
MANIFEST = 'd37715b9863dcf7477088d18e73e10325b71cac75bb0dcd7a74da53bae5e3067'
PUBLIC = 'f1af0e4e40a043fe974a50bf7caec32af9c20d7e595058614cab6ab30c8e756d'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def save(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


def inventory(root):
    rows = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        row = {'mode': s.st_mode, 'nlink': s.st_nlink}
        if stat.S_ISREG(s.st_mode):
            row.update(bytes=s.st_size, sha256=sha(p.read_bytes()))
        elif stat.S_ISLNK(s.st_mode):
            row['target'] = str(p.readlink())
        else:
            assert stat.S_ISDIR(s.st_mode), str(p)
        rows[p.relative_to(root).as_posix()] = row
    return rows


def run(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=150)
    row = {'command': list(map(str, cmd)), 'returncode': p.returncode,
           'stdout': p.stdout, 'stderr': p.stderr}
    assert p.returncode == 0, row
    return row


def instrument(source):
    # Execute the same cases and authentic COPIED verifier. The selected root's
    # FINAL-bound runner remains byte-identical; this derivative lives outside it.
    prefix = """def full_input_snapshot(root):
    out = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        row = {'mode': s.st_mode, 'nlink': s.st_nlink}
        if p.is_symlink(): row['target'] = os.readlink(p)
        elif p.is_file(): row.update(bytes=s.st_size, sha256=sha(p))
        out[str(p.relative_to(root))] = row
    return out

"""
    edits = [
        ('def main():', prefix + 'def main():'),
        ('        proc=subprocess.run(cmd,capture_output=True,text=True,timeout=40)',
         '        case_before=full_input_snapshot(c)\n'
         '        proc=subprocess.run(cmd,capture_output=True,text=True,timeout=40)\n'
         '        case_unchanged=case_before==full_input_snapshot(c)\n'
         '        assert case_unchanged, name'),
        ("'matched':ok,", "'matched':ok,'copied_input_unchanged':case_unchanged,"),
        ("        proc=subprocess.run([sys.executable,'-B','-c',script],capture_output=True,text=True,timeout=20)",
         "        audit_before=full_input_snapshot(work)\n"
         "        proc=subprocess.run([sys.executable,'-B','-c',script],capture_output=True,text=True,timeout=20)\n"
         "        audit_unchanged=audit_before==full_input_snapshot(work)\n"
         "        assert audit_unchanged, name"),
        ("'matched':proc.returncode!=0 and 'READ_ONLY' in proc.stderr,",
         "'matched':proc.returncode!=0 and 'READ_ONLY' in proc.stderr,'copied_input_unchanged':audit_unchanged,")
    ]
    for old, new in edits:
        assert source.count(old) == 1, old
        source = source.replace(old, new)
    return source


def main():
    before = inventory(AUTHOR)
    hashes = {'FINAL.json': FINAL, 'REPORT.md': REPORT,
              'packet/MANIFEST.json': MANIFEST, 'packet/public/report.md': PUBLIC}
    assert all(sha((AUTHOR / n).read_bytes()) == h for n, h in hashes.items())
    treepath = REPO / 'sources/preprints-tree.json'
    tb = treepath.read_bytes()
    assert sha(tb) == TREE
    tree = json.loads(tb)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {e['path']: e for e in tree['tree']}
    assert len(canonical) == 13223
    sources = json.loads((AUTHOR / 'packet/private/acquisition.json').read_text())
    assert len(sources) == 110 and len({s['canonical']['path'] for s in sources}) == 110
    assert sum(s['retained'] is True for s in sources) == 17
    assert sum(s['retained'] is False for s in sources) == 93
    for s in sources:
        e = s['canonical']
        assert e == canonical[e['path']] and e['type'] == 'blob'
        assert s['pinned_url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + e['path']
    save('canonical-replay.json', {
        'scope': 'INTEGRITY_ONLY', 'tree_sha256': TREE, 'entries': 13223,
        'truncated': False, 'source_records': 110, 'retained': 17, 'removed': 93,
        'all_full_canonical_records_and_pinned_raw_urls_matched': True,
        'removed_bodies_not_rehashed': True, 'external_hashes_matched': hashes,
        'mathematical_gate': False})
    save('integrity-replay.json', run([
        sys.executable, '-I', '-B', str(AUTHOR / 'verify.py'), '--root', str(AUTHOR),
        '--finalhash', FINAL, '--reporthash', REPORT, '--tree', str(treepath)]))
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=HERE) as temp:
        temp = Path(temp)
        copy = temp / 'author-copy'
        shutil.copytree(AUTHOR, copy, symlinks=True)
        assert sha((copy / 'FINAL.json').read_bytes()) == FINAL
        assert sha((copy / 'REPORT.md').read_bytes()) == REPORT
        source = (copy / 'run_controls.py').read_text()
        transformed = instrument(source)
        helper = temp / 'parent-instrumented-controls.py'
        helper.write_text(transformed)
        result = run([
            sys.executable, '-I', '-B', str(helper), '--root', str(copy),
            '--tree', str(treepath)])
        receipt = json.loads((copy / 'control-results.json').read_text())
        cases = receipt['cases']
        assert len(cases) == 16 and len({c['case'] for c in cases}) == 16
        assert all(c['matched'] and c['copied_input_unchanged'] for c in cases)
        assert sum(c['returncode'] == 0 for c in cases) == 1
        assert receipt['all_expected'] and receipt['original_unchanged']
        assert sha((copy / 'run_controls.py').read_bytes()) == sha(source.encode())
        save('copied-controls-replay.json', {
            'invocation': result, 'receipt': receipt,
            'scope': 'SAME_AUTHOR_CASES_WITH_PARENT_INPUT_SNAPSHOTS',
            'original_runner_sha256': sha(source.encode()),
            'instrumented_helper_sha256': sha(transformed.encode()),
            'helper_outside_selected_copy_root': True,
            'selected_root_runner_and_copied_verifiers_unmodified': True,
            'anchors_derived_only_after_parent_authenticated_copy': True,
            'original_author_control_results_preserved': True})
    after = inventory(AUTHOR)
    assert before == after
    save('author-unchanged.json', {
        'scope': 'INTEGRITY_ONLY', 'entire_author_root_unchanged': True,
        'before': before, 'after': after, 'temporary_copies_and_helper_removed': True})
    print(json.dumps({'integrity': 'PASS', 'canonical_records': 110, 'retained_sources': 17,
                      'same_controls_with_input_snapshots': 16, 'author_unchanged': True,
                      'mathematical_gate': False}))


if __name__ == '__main__':
    main()
