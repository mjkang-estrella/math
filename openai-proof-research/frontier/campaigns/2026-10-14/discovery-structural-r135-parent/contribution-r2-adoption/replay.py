#!/usr/bin/env python3
"""Parent review authentication/replay. Mathematical and contribution judgments remain separate."""
from pathlib import Path
import hashlib
import json
import runpy
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
PROJECT = PARENT.parents[3]
REVIEW = PARENT.parent / 't165p135-contribution-r2'
AUTHOR = PARENT.parent / 'fresh-structural-discovery-r135'
PRIOR = PARENT.parent / 't165p135-contribution-r1'
ANCHORS = {
    'FINAL.json': 'bf9b17004643358f9826f0a07bae8f5c5a880003f15b0b652d9cdb6e4be81833',
    'packet/MANIFEST.json': '9c37946b3aab0668a9749258af403c2bf3bf2f8e4fd3dc1889a769cb0e7ff516',
    'REPORT.md': 'bca81eb52480c4e419b513ad14a10ef33261fcf99a2862b6b0794a9ade7c3cac',
}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
snapshot = runpy.run_path(str(PARENT / 'replay.py'))['snapshot']

def main():
    before = {str(p): snapshot(p) for p in [AUTHOR, PRIOR, REVIEW]}
    for rel, h in ANCHORS.items():
        assert sha(REVIEW / rel) == h, rel
    initial = json.loads((REVIEW / 'work/start-inputs.json').read_text())
    more = json.loads((REVIEW / 'work/additional-inputs-start.json').read_text())
    stable = {rel: v['sha256'] for rel, v in initial.items() if v['type'] == 'file'}
    stable.update({rel: v['sha256'] for rel, v in more.items() if v.get('stability') != 'mutable_navigation_only'})
    for rel, h in stable.items():
        assert sha(PROJECT / rel) == h, rel
    sources = json.loads((REVIEW / 'packet/private/source-authentication.json').read_text())
    for r in sources:
        assert r['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + r['path']
        assert sha(PROJECT / r['original']) == sha(REVIEW / r['local']) == r['sha256']
    primary = json.loads((REVIEW / 'packet/private/primary-authentication.json').read_text())
    for r in primary:
        assert sha(PROJECT / r['original']) == sha(REVIEW / r['local']) == r['sha256']
        assert sha((PROJECT / r['original']).with_suffix('.txt')) == sha((REVIEW / r['local']).with_suffix('.txt')) == r['text_sha256']
    copies = json.loads((REVIEW / 'packet/private/input-copies.json').read_text())
    with tempfile.TemporaryDirectory(prefix='.r2-replay-', dir=HERE) as tmp:
        root = Path(tmp) / 'copy'
        shutil.copytree(REVIEW, root)
        copied_before = snapshot(root)
        cmd = [sys.executable, '-B', str(root / 'packet/public/verify.py'), '--root', str(root),
               '--project', str(PROJECT), '--finalhash', ANCHORS['FINAL.json'],
               '--manifesthash', ANCHORS['packet/MANIFEST.json'], '--reporthash', ANCHORS['REPORT.md']]
        run = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        verification = {'exit': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr}
        assert run.returncode == 0, verification
        # The unchanged copied control script derives PROJECT from its install depth.
        # Route only that in-memory execution global to the actual read-only project.
        # No original/copied program bytes or payload bindings are modified.
        wrapper = "import runpy,sys; from pathlib import Path; m=runpy.run_path(sys.argv[1]); m['main'].__globals__['PROJECT']=Path(sys.argv[2]); sys.argv=[sys.argv[1]]; m['main']()"
        run = subprocess.run([sys.executable, '-B', '-c', wrapper,
            str(root / 'packet/public/control-tests.py'), str(PROJECT)], capture_output=True, text=True, timeout=60)
        controls = {'exit': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr}
        assert run.returncode == 0, controls
        receipt = json.loads((root / 'packet/public/control-results.json').read_text())
        assert receipt['all_expected'] and len(receipt['cases']) == 19
        run = subprocess.run([sys.executable, '-B', str(root / 'packet/public/reduction-check.py')],
            capture_output=True, text=True, timeout=60)
        diagnostic = {'exit': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr}
        assert run.returncode == 0 and json.loads(run.stdout) == json.loads((root / 'packet/public/reduction-results.json').read_text())
        assert copied_before == snapshot(root), 'copied payload changed'
    roots_unchanged = {str(p): before[str(p)] == snapshot(p) for p in [AUTHOR, PRIOR, REVIEW]}
    stable_unchanged = all(sha(PROJECT / rel) == h for rel, h in stable.items())
    assert all(roots_unchanged.values()) and stable_unchanged
    result = {'kind': 'PARENT_ARTIFACT_AUTHENTICATION_NOT_MATHEMATICAL_GATE', 'all_expected': True,
        'anchors': ANCHORS, 'verification': verification, 'copied_controls': controls,
        'copied_control_cases': receipt['cases'], 'reduction_diagnostic': diagnostic,
        'original_roots_unchanged': roots_unchanged, 'stable_external_hashes': stable,
        'stable_external_files_unique': len(stable), 'stable_external_files_unchanged': stable_unchanged,
        'initial_snapshot_entries': len(initial), 'initial_file_entries': sum(v['type'] == 'file' for v in initial.values()),
        'additional_stable_file_entries': sum(v.get('stability') != 'mutable_navigation_only' for v in more.values()),
        'mutable_navigation_entries': sum(v.get('stability') == 'mutable_navigation_only' for v in more.values()),
        'canonical_source_bodies': len(sources), 'primary_pdf_text_pairs': len(primary), 'input_copies': len(copies),
        'coverage_limits': 'Exact persistent review tree and metadata verified under detached anchors;19 copied '
        'seal controls and finite reduction diagnostics replayed. Copied control script PROJECT global routed '
        'in memory to the actual project because copy depth changes; program bytes unchanged. Original verifier '
        'stable_external_files counter includes an ignored mutable-navigation entry; parent separately counts '
        'stable and mutable bindings above. Original read/binding timing limits, unread primary bodies and late '
        'parent additions remain; no syscall-denial, historic-read, priority, full correctness or portable-release claim.'}
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['all_expected','initial_snapshot_entries','initial_file_entries',
        'additional_stable_file_entries','mutable_navigation_entries','stable_external_files_unique',
        'canonical_source_bodies','primary_pdf_text_pairs','input_copies']}))

if __name__ == '__main__':
    main()
