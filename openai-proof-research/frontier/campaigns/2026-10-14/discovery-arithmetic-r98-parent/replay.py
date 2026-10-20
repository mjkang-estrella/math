#!/usr/bin/env python3
"""Copied artifact intake only; does not assign a mathematical or contribution gate."""
import hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
ROUND = "fresh-arithmetic-discovery-r98"
FINAL = "19977966e5ff34cb1b55661b1c5820caf2916413866b9a2c4df55c33a642db25"
MANIFEST = "e8f4323fb2ac8b1bb3a25e9c387890daf287ad2196198ba8652ab36547fcfa39"
REPORT = "e5c51f3e0c24602642d31a388549fbe4fd284dcfe7fe26caa33219b609fe29db"
KIND = "arithmetic"

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def snapshot(root):
    out = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        rec = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode):
            rec += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode):
            rec += [os.readlink(p)]
        out[p.relative_to(root).as_posix()] = rec
    return out

def run(args, cwd):
    p = subprocess.run([sys.executable, '-B', *args], cwd=cwd, capture_output=True,
                       text=True, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    return {'exit': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}

def main():
    parent = Path(__file__).resolve().parent
    author = parent.parent / ROUND
    repo = author.parents[3]
    assert sha(author / 'FINAL.json') == FINAL
    assert sha(author / 'packet/MANIFEST.json') == MANIFEST
    assert sha(author / 'REPORT.md') == REPORT
    before = snapshot(author)
    code = 'packet/code' if KIND == 'arithmetic' else 'packet/public'
    common = ['--root', '.', '--final-sha256', FINAL, '--report-sha256', REPORT]
    if KIND == 'arithmetic':
        common += ['--tree', str(repo / 'sources/preprints-tree.json')]
    original_verify = run([code + '/verify.py', *common], author)
    # Also bind copied histories/context to their current project originals.
    pairs = []
    if KIND == 'arithmetic':
        reg = json.loads((author / 'packet/public/context-register.json').read_text())['copies']
        pairs = [(author / 'packet' / r['local'], repo / r['origin']) for r in reg]
    else:
        for rel in ['history', 'context']:
            reg = json.loads((author / ('packet/private/' + rel + '/register.json')).read_text())
            pairs += [(author / r['local'], repo / r['origin']) for r in reg]
    bindings = [{'copy': str(p.relative_to(author)), 'origin': str(q.relative_to(repo)),
                 'match': sha(p) == sha(q)} for p, q in pairs]
    with tempfile.TemporaryDirectory(prefix='copied-replay-', dir=parent) as td:
        copy = Path(td) / 'root'
        shutil.copytree(author, copy, symlinks=True)
        verified = run([code + '/verify.py', *common], copy)
        wrong_args = list(common)
        wrong_args[wrong_args.index('--final-sha256') + 1] = '0' * 64
        wrong = run([code + '/verify.py', *wrong_args], copy)
        controls = run([code + '/controls.py', *common], copy)
        if KIND == 'arithmetic':
            receipt = json.loads((copy / 'integrity-results.json').read_text())
        else:
            receipt = json.loads(controls['stdout'])
    unchanged = before == snapshot(author)
    ok = (original_verify['exit'] == 0 and verified['exit'] == 0 and wrong['exit'] != 0
          and controls['exit'] == 0 and receipt['all_expected']
          and all(r['match'] for r in bindings) and unchanged)
    out = {'kind': 'PARENT_ARTIFACT_INTAKE_ONLY', 'mathematical_gate': False,
           'detached_anchors': {'final': FINAL, 'manifest': MANIFEST, 'report': REPORT},
           'original_verify': original_verify, 'copy_verify': verified,
           'wrong_final': wrong, 'copied_controls': controls,
           'copied_controls_receipt': receipt, 'current_project_bindings': bindings,
           'whole_author_root_unchanged': unchanged, 'all_expected': ok}
    (parent / 'replay.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({'round': ROUND, 'all_expected': ok,
                      'cases': len(receipt['cases']), 'original_unchanged': unchanged,
                      'current_project_bindings': len(bindings)}))
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
