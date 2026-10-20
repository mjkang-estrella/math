#!/usr/bin/env python3
"""Authenticate and replay the sealed checkpoint left before a provider usage-limit failure."""
from pathlib import Path
import hashlib
import json
import runpy
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
PROJECT = HERE.parents[3]
AUTHOR = BASE / 'fresh-arithmetic-discovery-r100'
FINAL = 'bf0a079c6e0314ebd6e2e4abed7b09d0ab7d24379e0b78096cc9eb041799e144'
REPORT = '909ae3cd4c7439359da7b58b75c1737f185f8062c56d7466b0254990fe242e9a'
RECEIPT = 'e26c20a8731af30beb4e45664038d6d88105996f9cd012a9dd50b2d5e79d1fb3'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
snapshot = runpy.run_path(str(BASE / 'discovery-structural-r135-parent/replay.py'))['snapshot']

def main():
    before = snapshot(AUTHOR)
    assert sha(AUTHOR / 'FINAL.json') == FINAL
    assert sha(AUTHOR / 'REPORT.md') == REPORT
    assert sha(AUTHOR / 'integrity-results.json') == RECEIPT
    tree = PROJECT / 'sources/preprints-tree.json'
    t = json.loads(tree.read_text())
    assert t['truncated'] is False and len(t['tree']) == 13223
    mapping = {
        'AGENTS.md': PROJECT / 'AGENTS.md',
        'ford-totients-r2-retrieval.json': BASE / 'fresh-arithmetic-discovery-r2/literature/retrieval.json',
        'ford-totients-r2-text-extraction.txt': BASE / 'fresh-arithmetic-discovery-r2/literature/ford-totients.txt',
        'fresh-arithmetic-r100-brief.txt': BASE / 'expanded-target-2026-10-17/fresh-arithmetic-r100-brief.txt',
        'i99-quantitative-arithmetic-patterns-discovery.md': PROJECT / 'frontier/iterations/i99-quantitative-arithmetic-patterns-discovery.md',
        'r95-family-history-counts.txt': BASE / 'fresh-arithmetic-discovery-r95/packet/private/history/family-history-counts.txt',
        'r99-contribution-r1-adoption.json': BASE / 'discovery-arithmetic-r99-parent/contribution-r1-adoption/adoption.json',
        'r99-parent-disposition.md': BASE / 'discovery-arithmetic-r99-parent/disposition.md',
        'r99-public-reading-limits.md': BASE / 'fresh-arithmetic-discovery-r99/packet/public/reading-limits.md',
        'r99-public-report.md': BASE / 'fresh-arithmetic-discovery-r99/packet/public/report.md',
        'r99-public-screens.md': BASE / 'fresh-arithmetic-discovery-r99/packet/public/screens.md',
        'research-brief-2026-10-20.txt': BASE / 'expanded-target-2026-10-17/research-brief-2026-10-20.txt',
        't024w-proof-r1-report.md': BASE / 't024w-proof-r1/report.md',
        'totient-recovery-parent-disposition.json': BASE / 'totient-recovery-parent/disposition.json',
        'totient-recovery-r3-checkpoint.md': BASE / 'totient-recovery-r3/checkpoint.md',
        'totient-recovery-r3-scope.md': BASE / 'totient-recovery-r3/scope.md',
    }
    contexts = json.loads((AUTHOR / 'packet/public/context-register.json').read_text())['copies']
    deps = {}
    for r in contexts:
        original = mapping[Path(r['local']).name]
        assert sha(original) == r['sha256'] == sha(AUTHOR / 'packet' / r['local']), str(original)
        deps[str(original.relative_to(PROJECT))] = r['sha256']
    deps['sources/preprints-tree.json'] = sha(tree)
    deps['sources/upstream.json'] = sha(PROJECT / 'sources/upstream.json')
    with tempfile.TemporaryDirectory(prefix='.r100-replay-', dir=HERE) as tmp:
        root = Path(tmp) / 'copy'
        shutil.copytree(AUTHOR, root)
        copy_before = snapshot(root)
        common = ['--root', str(root), '--tree', str(tree), '--final-sha256', FINAL, '--report-sha256', REPORT]
        runs = {}
        for name in ['verify', 'controls']:
            proc = subprocess.run([sys.executable, '-B', str(root / ('packet/code/' + name + '.py')), *common],
                                  capture_output=True, text=True, timeout=60)
            runs[name] = {'exit': proc.returncode, 'stdout': proc.stdout, 'stderr': proc.stderr}
            assert proc.returncode == 0, runs[name]
            if name == 'verify':
                assert copy_before == snapshot(root), 'verifier wrote copied inputs'
        receipt = json.loads((root / 'integrity-results.json').read_text())
        assert receipt['all_expected'] and len(receipt['cases']) == 16
        assert receipt['author_root_unchanged_during_replay']
        copy_after = snapshot(root)
        assert {k:v for k,v in copy_before.items() if k != 'integrity-results.json'} == {
            k:v for k,v in copy_after.items() if k != 'integrity-results.json'}
    originals_unchanged = all(sha(PROJECT / p) == h for p, h in deps.items())
    whole_unchanged = before == snapshot(AUTHOR)
    assert originals_unchanged and whole_unchanged
    final = json.loads((AUTHOR / 'FINAL.json').read_text())
    out = {'kind': 'FAILED_TASK_SEALED_PREFREEZE_CHECKPOINT_ARTIFACT_REPLAY', 'all_expected': True,
        'final_sha256': FINAL, 'manifest_sha256_bound_by_final': final['manifest_sha256'],
        'report_sha256': REPORT, 'original_integrity_receipt_sha256': RECEIPT,
        'runs': runs, 'copied_control_receipt': receipt, 'whole_author_root_unchanged': whole_unchanged,
        'history_bindings': len(contexts), 'external_originals': deps, 'external_originals_unchanged': originals_unchanged,
        'coverage_limits': 'Packet exact files/directories/modes/single links and source/history hashes checked. '
        'Audit hook rejects the enumerated writes/network events; no comprehensive syscall-denial or malicious '
        'resealing claim. Notes/work are outside author seal but parent whole-root preservation snapshot covers '
        'this replay. No mathematical, contribution, priority or portable-release gate.'}
    (HERE / 'replay.json').write_text(json.dumps(out, indent=2) + '\n')
    (HERE / 'original-snapshot.json').write_text(json.dumps(before, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'all_expected': True, 'copied_cases': len(receipt['cases']),
        'history_bindings': len(contexts), 'external_originals': len(deps), 'whole_original_unchanged': whole_unchanged}))

if __name__ == '__main__':
    main()
