#!/usr/bin/env python3
"""Local consistency replay; no detached T3 authentication or mathematical gate."""
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parent / 'fresh-structural-discovery-r125'
REPO = HERE.parents[3]
HASHES = {
    'FINAL.json': 'b177b36d6ef39750a4621d0fd1f4c73a5d4891c74fc0cd6d9041b0d5eb7aa41e',
    'REPORT.md': 'b89f5d434fca85f54757202e50959546c6224f8ac7beadac3d75cd64dfb4cee4',
    'packet/MANIFEST.json': '4c6aaaa4b6c31dccd03ca58677bd3279f6de0646f3366e7341493d32b20de6cc',
    'packet/public/proof.md': 'fc725dd2d70ca3a5a52bcfdca7da954e674a3157353b831dd2caf6badd097881',
    'packet/public/FROZEN-SCOPE.md': 'ec09396badbea0351a0eb2f8bdb7b780e1d74ffdace92bb04114cccdc5be4a22',
}
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def inventory(root):
    rows = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        row = {'mode': s.st_mode, 'nlink': s.st_nlink}
        if stat.S_ISREG(s.st_mode):
            row.update(bytes=s.st_size, sha256=sha(p.read_bytes()))
        else:
            assert stat.S_ISDIR(s.st_mode), str(p)
        rows[p.relative_to(root).as_posix()] = row
    return rows


def run(command):
    result = subprocess.run(command, capture_output=True, text=True, timeout=150)
    assert result.returncode == 0, (command, result.returncode, result.stdout, result.stderr)
    return {'returncode': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr}


def main():
    before = inventory(AUTHOR)
    assert all(sha((AUTHOR / n).read_bytes()) == h for n, h in HASHES.items())
    tree_bytes = (REPO / 'sources/preprints-tree.json').read_bytes()
    assert sha(tree_bytes) == TREE
    tree = json.loads(tree_bytes)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    canonical = {r['path']: r for r in tree['tree']}
    assert len(canonical) == 13223
    packet = AUTHOR / 'packet'
    contexts = json.loads((packet / 'private/context-register.json').read_text())
    tree_records = [r for r in contexts if r['origin'] == 'sources/preprints-tree.json']
    assert len(tree_records) == 1
    assert (packet / tree_records[0]['local']).read_bytes() == tree_bytes
    records = json.loads((packet / 'private/upstream-register.json').read_text())
    assert len(records) == len({r['canonical']['path'] for r in records}) == 39
    for r in records:
        c = r['canonical']
        assert c == canonical[c['path']] and c['type'] == 'blob'
        assert r['url'] == f"https://raw.githubusercontent.com/openai/math/{PIN}/{c['path']}"
    common = ['--finalhash', HASHES['FINAL.json'], '--reporthash', HASHES['REPORT.md']]
    checked = run([sys.executable, '-I', '-B', str(packet / 'public/verify.py'),
                   '--root', str(AUTHOR), *common])
    with tempfile.TemporaryDirectory(prefix='replay-', dir=HERE) as temp:
        copied = Path(temp) / 'author-copy'
        shutil.copytree(AUTHOR, copied, symlinks=True)
        copied_check = run([sys.executable, '-I', '-B', str(copied / 'packet/public/controls.py'),
                            '--root', str(copied), '--out', 'parent-controls', *common])
        controls = json.loads((copied / 'parent-controls/receipt.json').read_text())
        cases = controls['cases']
        assert len(cases) == len({r['case'] for r in cases}) == 26
        assert controls['all_expected'] and controls['whole_preexisting_owned_root_unchanged']
        assert all(r['expected_result'] and r['unchanged_copy'] for r in cases)
        assert sum(r['returncode'] == 0 for r in cases) == 1
        assert next(r for r in cases if r['case'] == 'baseline')['returncode'] == 0
    finite = run([sys.executable, '-I', '-B', str(packet / 'public/finite_disintegration.py')])
    assert json.loads(finite['stdout']) == json.loads((packet / 'public/finite-disintegration.json').read_text())
    after = inventory(AUTHOR)
    assert before == after
    receipt = {
        'status': 'LOCAL_CONSISTENCY_REPLAY_ONLY',
        'anchor_provenance': 'Hashes observed from local files; detached T3 result unavailable. Internal consistency is not authenticated worker-to-parent transfer.',
        'local_hashes': HASHES,
        'canonical_tree_sha256': TREE,
        'canonical_entries': 13223,
        'canonical_records': len(records),
        'retained_sources': sum(r['retained'] for r in records),
        'removed_sources': sum(not r['retained'] for r in records),
        'all_full_canonical_records_and_raw_urls_matched': True,
        'verifier': checked,
        'copied_controls_invocation': copied_check,
        'copied_controls': controls,
        'finite_diagnostic': finite,
        'whole_actual_author_root_unchanged': before == after,
        'whole_author_inventory_sha256': sha(json.dumps(before, sort_keys=True).encode()),
        'mathematical_gate': False,
        'contribution_gate': False,
        'count_change': 0,
    }
    (HERE / 'replay.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'copied_controls': len(cases),
                      'actual_author_root_unchanged': True, 'detached_transfer_authenticated': False,
                      'mathematical_gate': False, 'count_change': 0}))


if __name__ == '__main__':
    main()
