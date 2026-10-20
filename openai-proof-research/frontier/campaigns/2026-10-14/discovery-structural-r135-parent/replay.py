#!/usr/bin/env python3
"""Local parent artifact replay; no mathematical verdict or portable-release claim."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[3]
AUTHOR = HERE.parent / 'fresh-structural-discovery-r135'
ANCHORS = {
    'FINAL.json': '9e01e0dbcdab7665d6ce58c904291cb3caeaef9e54f5befb023336abe21f6be6',
    'packet/MANIFEST.json': '6b997e3d8605220fc4845528d8213356c792e7d674eab50d7be9d16d4730eae5',
    'REPORT.md': '4ecc09d4de9fe7e2f5e095b7b0ac2215a6665438898378e6ee8c91de6b0e037e',
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def snapshot(root):
    out = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        rel = str(p.relative_to(root))
        if stat.S_ISLNK(s.st_mode):
            out[rel] = {'type': 'symlink', 'target': os.readlink(p)}
        elif stat.S_ISDIR(s.st_mode):
            out[rel] = {'type': 'dir', 'mode': stat.S_IMODE(s.st_mode)}
        elif stat.S_ISREG(s.st_mode):
            out[rel] = {'type': 'file', 'mode': stat.S_IMODE(s.st_mode),
                        'nlink': s.st_nlink, 'bytes': s.st_size, 'sha256': sha(p)}
        else:
            raise AssertionError('special file: ' + str(p))
    return out

def main():
    before = snapshot(AUTHOR)
    dependencies = ['AGENTS.md', 'sources/upstream.json', 'sources/preprints-tree.json',
        'frontier/campaigns/2026-10-14/expanded-target-2026-10-17/research-brief-2026-10-20.txt',
        'frontier/campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r135-brief.txt',
        'frontier/campaigns/2026-10-14/discovery-structural-r134-parent/disposition.md',
        'frontier/campaigns/2026-10-14/discovery-structural-r134-parent/contribution-r1-adoption/adoption.json',
        'frontier/campaigns/2026-10-14/t184i134-contribution-r1/packet/public/review.md',
        'frontier/campaigns/2026-10-14/t184i134-contribution-r1/packet/public/reading-limits.md']
    dep_before = {p: sha(PROJECT / p) for p in dependencies}
    for rel, h in ANCHORS.items():
        assert sha(AUTHOR / rel) == h, rel
    tree = json.loads((PROJECT / 'sources/preprints-tree.json').read_text())
    assert tree.get('truncated') is False and len(tree['tree']) == 13223
    cases = []
    with tempfile.TemporaryDirectory(prefix='.replay-', dir=HERE) as tmp:
        tmp = Path(tmp)
        names = ['baseline', 'missing-anchor', 'wrong-anchor', 'tampered-proof',
            'tampered-scope', 'tampered-report', 'extra-file', 'tampered-source',
            'tampered-primary', 'tampered-manifest', 'missing-proof', 'extra-directory', 'symlink']
        for name in names:
            root = tmp / name
            shutil.copytree(AUTHOR, root, symlinks=True)
            targets = {'tampered-proof': 'packet/public/proof.md',
                'tampered-scope': 'packet/public/frozen-statement.md',
                'tampered-report': 'REPORT.md', 'tampered-manifest': 'packet/MANIFEST.json',
                'tampered-source': 'packet/private/source/preprints__The-crossing-number-of-complete-bipartite-graphs-September-23-2026__README.md',
                'tampered-primary': 'packet/private/primary/schaefer-ds21-survey.pdf'}
            if name in targets:
                p = root / targets[name]
                p.write_bytes(p.read_bytes() + b'\nparent integrity mutation\n')
            if name == 'extra-file':
                (root / 'packet/public/unlisted.txt').write_text('extra\n')
            if name == 'missing-proof':
                (root / 'packet/public/proof.md').unlink()
            if name == 'extra-directory':
                (root / 'packet/public/unlisted-empty').mkdir()
            if name == 'symlink':
                (root / 'packet/public/unlisted-link').symlink_to('proof.md')
            cmd = [sys.executable, '-B', str(root / 'packet/public/verify.py'),
                   '--root', str(root), '--project', str(PROJECT)]
            if name != 'missing-anchor':
                cmd += ['--finalhash', '0' * 64 if name == 'wrong-anchor' else ANCHORS['FINAL.json']]
            copy_before = snapshot(root)
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
            unchanged = copy_before == snapshot(root)
            expected = proc.returncode == 0 if name == 'baseline' else proc.returncode != 0
            cases.append({'case': name, 'exit': proc.returncode, 'as_expected': expected,
                'copied_input_unchanged': unchanged, 'stdout': proc.stdout, 'stderr': proc.stderr})
            if name == 'baseline':
                sanity_before = snapshot(root)
                sanity_proc = subprocess.run([sys.executable, '-B', str(root / 'packet/public/sanity.py')],
                    capture_output=True, text=True, timeout=60, cwd=root)
                sanity = {'exit': sanity_proc.returncode, 'stdout': sanity_proc.stdout,
                    'stderr': sanity_proc.stderr, 'copied_input_unchanged': sanity_before == snapshot(root)}
    after = snapshot(AUTHOR)
    deps_unchanged = dep_before == {p: sha(PROJECT / p) for p in dependencies}
    all_expected = all(c['as_expected'] and c['copied_input_unchanged'] for c in cases)
    all_expected &= before == after and deps_unchanged and sanity['exit'] == 0 and sanity['copied_input_unchanged']
    record = {'kind': 'PARENT_ARTIFACT_REPLAY_NOT_MATHEMATICAL_GATE', 'anchors': ANCHORS,
        'cases': cases, 'sanity': sanity, 'whole_original_root_unchanged': before == after,
        'external_dependencies': dep_before, 'external_dependencies_unchanged': deps_unchanged,
        'all_expected': bool(all_expected), 'coverage_limits':
        'Verifier checks exact packet files/directories and rejects packet symlinks/special entries; '
        'does not bind modes/hardlinks or outside notes, sidecars and control receipt. Parent snapshots '
        'cover whole original author root and copied cases with modes/nlink. Preservation observation, '
        'not syscall-level write denial. Source/primary receipt authentication is not a mathematical gate.'}
    (HERE / 'replay.json').write_text(json.dumps(record, indent=2) + '\n')
    (HERE / 'original-snapshot.json').write_text(json.dumps(before, indent=2, sort_keys=True) + '\n')
    assert all_expected, record
    print(json.dumps({'all_expected': bool(all_expected), 'copied_cases': len(cases),
        'sanity': sanity, 'original_unchanged': before == after, 'external_inputs': len(dependencies)}))

if __name__ == '__main__':
    main()
