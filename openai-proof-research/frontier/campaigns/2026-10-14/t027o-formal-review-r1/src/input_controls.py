#!/usr/bin/env python3
"""Reviewer controls on disposable /var/tmp copies of the frozen T027O formal input (MIT).

Identity part: runs the author's own verify.py on mutated copies and records the reason.
Semantic part: compiles mutated copies of the Lean sources and requires rejection.
Never writes inside the frozen input. No mathematical verdict is produced by this script.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

INPUT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/t027o-formal-v1')
ANCHOR = 'b35948fddec735c7d9f0ed742d8158f4787f571cd69175a01f4db7ce2add46a4'
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
CACHE = INPUT.parent / 'formal/.lake/packages'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def snapshot(root):
    return {p.relative_to(root).as_posix(): sha(p.read_bytes()) for p in sorted(root.rglob('*')) if p.is_file()}

def verify(root, anchor):
    r = subprocess.run(['python3', '-B', str(root / 'verify.py'), '--anchor', anchor],
                       capture_output=True, text=True, timeout=60)
    return r.returncode, (r.stdout + r.stderr).strip()

def identity_cases(base):
    def edit(path, old, new):
        data = path.read_bytes()
        assert data.count(old) == 1, (path, old)
        path.write_bytes(data.replace(old, new))
    cases = {
        'positive': (lambda d: None, None, 'PASS_IDENTITY_ONLY'),
        'wrong-anchor': (lambda d: None, 'f' * 64, 'external anchor mismatch'),
        'semantic-one-byte-T027O': (lambda d: edit(d / 'T027O.lean', b'M i k * M k j * M j i \xe2\x89\xa0 0', b'M i k * M k j * M j i = 0'), None, 'exact inventory mismatch'),
        'changed-controls': (lambda d: edit(d / 'Controls.lean', b'!![0, 1, 1; 2, 0, 1; 1, 3, 0]', b'!![0, 1, 1; 1, 0, 1; 1, 1, 0]'), None, 'exact inventory mismatch'),
        'deleted-receipt': (lambda d: (d / 'checks/receipt.json').unlink(), None, 'exact inventory mismatch'),
        'extra-check-file': (lambda d: (d / 'checks/extra.log').write_text(''), None, 'exact inventory mismatch'),
        'manifest-edited': (lambda d: edit(d / 'manifest.json', b'"bytes": 3229', b'"bytes": 3230'), None, 'external anchor mismatch'),
        'readme-scope-edit': (lambda d: edit(d / 'README.md', b'is not an independent formal review', b'is an independent formal review'), None, 'exact inventory mismatch'),
    }
    out = []
    for name, (mutate, anchor, expect) in cases.items():
        d = base / ('id-' + name)
        shutil.copytree(INPUT, d)
        mutate(d)
        code, text = verify(d, anchor or ANCHOR)
        ok = (code == 0) == (name == 'positive') and expect in text
        if not ok:
            raise AssertionError((name, code, text))
        out.append({'case': name, 'accepted': code == 0, 'reason': text})
    return out

def lean_env(build):
    lock = json.loads((INPUT / 'lake-manifest.json').read_text())
    libs = [str((CACHE / e['name'] / '.lake/build/lib/lean').resolve()) for e in lock['packages']
            if (CACHE / e['name'] / '.lake/build/lib/lean').is_dir()]
    return dict(os.environ, LEAN_PATH=os.pathsep.join([str(build)] + libs), GIT_OPTIONAL_LOCKS='0')

def sorry_body(support):
    head = '∃ h : ι → K, ∀ i j, E i j = (h i - h j) * M i j := by\n'
    assert support.count(head) == 1
    start = support.index(head) + len(head)
    return support[:start] + '  sorry\n\nend T027O\n'

def compile_cases(base):
    # Each case mutates the support or controls source and must make compilation fail
    # or, for 'sorry', must surface sorryAx/warning.
    support = (INPUT / 'T027O.lean').read_text()
    controls = (INPUT / 'Controls.lean').read_text()
    generic_hyp = ("    (hgeneric : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →\n"
                   "      M i j * M j k * M k i - M i k * M k j * M j i ≠ 0) :\n")
    assert support.count(generic_hyp) == 1
    pair_hyp = "    (hpair : ∀ i j, i ≠ j → E i j * M j i + M i j * E j i = 0)\n"
    assert support.count(pair_hyp) == 1
    cases = {
        'baseline': (support, controls, True),
        'delete-hgeneric': (support.replace(generic_hyp, '    :\n').replace(
            '    (htri : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →\n      cycleDerivative M E i j k = 0)\n    :\n',
            '    (htri : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →\n      cycleDerivative M E i j k = 0) :\n'), controls, False),
        'delete-hpair': (support.replace(pair_hyp, ''), controls, False),
        'flip-cycle-sign': (support.replace('M i k * M k j * E j i\n', '- M i k * M k j * E j i\n', 1).replace(
            'M i k * E k j * M j i + - M', 'M i k * E k j * M j i - M'), controls, False),
        'sorry-proof': (sorry_body(support), controls, False),
        'controls-generic-dropped-from-symmetric': (support, controls.replace(
            'theorem not_diagonal_commutator', 'theorem symmetric_bad : ∃ h : Fin 3 → ℚ, ∀ i j, cycleE i j = (h i - h j) * symmetricM i j := by\n  apply T027O.principal_minor_rigidity 0 symmetricM cycleE nonzero_off_diagonal stationary_diagonal\n    (fun i j _ => stationary_pairs i j) (fun i j k _ _ _ => stationary_cycles i j k)\n  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [symmetricM]\n\ntheorem not_diagonal_commutator', 1), False),
    }
    results = []
    for name, (src, ctl, should_pass) in cases.items():
        b = base / ('lean-' + name)
        b.mkdir()
        (b / 'T027O.lean').write_text(src)
        (b / 'Controls.lean').write_text(ctl)
        env = lean_env(b)
        r1 = subprocess.run([str(LEAN), '-o', 'T027O.olean', 'T027O.lean'], cwd=b, env=env, capture_output=True, text=True)
        log = r1.stdout + r1.stderr
        ok = r1.returncode == 0 and not re.search(r'\b(?:error|warning):', log)
        if ok:
            r2 = subprocess.run([str(LEAN), '-o', 'Controls.olean', 'Controls.lean'], cwd=b, env=env, capture_output=True, text=True)
            log += r2.stdout + r2.stderr
            ok = r2.returncode == 0 and not re.search(r'\b(?:error|warning):', log)
        if name == 'sorry-proof':
            assert 'sorry' in log, log
        if ok != should_pass:
            raise AssertionError((name, ok, log[:3000]))
        first = next((l for l in log.splitlines() if re.search(r'\b(?:error|warning)', l)), '')
        results.append({'case': name, 'clean_build': ok, 'first_diagnostic': first[:300]})
    return results

def main():
    before = snapshot(INPUT)
    assert sha((INPUT / 'manifest.json').read_bytes()) == ANCHOR
    with tempfile.TemporaryDirectory(prefix='t027o-review-input-controls-', dir='/var/tmp') as tmp:
        base = Path(tmp)
        identity = identity_cases(base)
        semantic = compile_cases(base)
    after = snapshot(INPUT)
    assert before == after, 'frozen input changed'
    print(json.dumps({'identity_only_for_identity_cases': True, 'input_manifest_sha256': ANCHOR,
                      'input_files_unchanged': len(after), 'identity': identity,
                      'lean_mutations': semantic}, indent=2))

if __name__ == '__main__':
    main()
