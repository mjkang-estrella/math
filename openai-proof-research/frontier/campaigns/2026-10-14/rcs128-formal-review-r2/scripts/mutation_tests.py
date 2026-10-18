#!/usr/bin/env python3
"""Copied-packet mutation tests of the frozen RCS128 rebuild/verify harness (review r2).

MIT license, Myeongjin Kang (review packet). For each case: copy the frozen
package byte-for-byte to a NEW directory, apply one source mutation, run the
copied rebuild.py (one compiler at a time, timeout per run) and the copied
verify.py with the ORIGINAL external anchor. The frozen package is only read.
Run inside an external memory limit (systemd-run --user --scope -p MemoryMax=3G).
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ANCHOR = 'c3a051864862ebf53c24fce85da991f2e1da18340d38afdae238f3a160361963'

DEFICIT = '    2 * k + 1 ≤ delta * (k + 1) := by'
FINAL = '''    output ≤ 2 * optimum := by
  omega'''
CASES = {
    'M0-unmodified-copy': ('expect PASS (positive control of the copied harness)', None),
    'M1-false-statement': ('expect FAIL: genuine Lean error', ('RCS128.lean', DEFICIT,
                           '    2 * k + 3 ≤ delta * (k + 1) := by')),
    'M2-dropped-free-hypothesis': ('expect FAIL: genuine Lean error', ('RCS128.lean',
                                   '    (hfree : ∀ x ∈ s, rho x ≠ x) : Even s.card := by',
                                   '    : Even s.card := by')),
    'M3-warning-only': ('expect FAIL: deprecation warning rejected', ('Controls.lean',
                        'end RCS128Controls',
                        '@[deprecated "control" (since := "2026-10-17")] theorem oldT : True := trivial\n'
                        'theorem useOld : True := oldT\n\nend RCS128Controls')),
    'M4-sorry': ('expect FAIL: forbidden token', ('RCS128.lean', FINAL,
                 '    output ≤ 2 * optimum := by\n  sorry')),
    'M5-private-axiom': ('expect FAIL: nonstandard axiom (regex misses `private axiom`)',
                         ('RCS128.lean', '/-- This is the candidate\'s final factor accounting',
                          'private axiom cheat : (2 : ℕ) = 3\n\n'
                          '/-- This is the candidate\'s final factor accounting')),
    'M5b-private-axiom-no-warning': ('expect FAIL: nonstandard axiom in #print axioms '
                                     '(regex misses `private axiom`; no warning emitted)',
                                     ('RCS128.lean', '/-- This is the candidate\'s final factor accounting',
                                      'private axiom cheat : (2 : ℕ) = 3\n\n'
                                      '/-- This is the candidate\'s final factor accounting')),
    'M5c-private-axiom-new-theorem': ('expect FAIL: nonstandard axiom in #print axioms '
                                      '(regex misses `private axiom`; no warning emitted)',
                                      ('RCS128.lean', '/-- This is the candidate\'s final factor accounting',
                                       'private axiom cheat : (2 : ℕ) = 3\n\n'
                                       'theorem cheat_use : (2 : ℕ) = 3 := cheat\n\n'
                                       '/-- This is the candidate\'s final factor accounting')),
    'M6-native-decide': ('expect FAIL: forbidden token', ('Controls.lean',
                         '0 < (1 : ℕ) ∧ ¬ ((2 : ℕ) * 1 + 1 ≤ 1 * (1 + 1)) := by\n  decide',
                         '0 < (1 : ℕ) ∧ ¬ ((2 : ℕ) * 1 + 1 ≤ 1 * (1 + 1)) := by\n  native_decide')),
    'M7-weakened-statement': ('expect PASS of build (harness checks compilation, not intended '
                              'statements); verify.py must FAIL', ('RCS128.lean', FINAL,
                              '    output ≤ 4 * optimum := by\n  omega')),
    'M8-controls-error': ('expect FAIL: genuine Lean error', ('Controls.lean',
                          '¬ (4 : ℕ) ≤ 2 * 1 := by', '¬ (4 : ℕ) ≤ 2 * 2 := by')),
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--frozen', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--only', nargs='*', default=None)
    args = parser.parse_args()
    frozen = args.frozen.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
    summary = {}
    for name, (expectation, mutation) in CASES.items():
        if args.only is not None and name not in args.only:
            continue
        case = out / name
        packet = case / 'packet'
        shutil.copytree(frozen, packet, symlinks=True)
        if mutation is not None:
            filename, old, new = mutation
            path = packet / filename
            text = path.read_text()
            if name == 'M5b-private-axiom-no-warning':
                text = text.replace('    output ≤ 2 * optimum := by\n  omega',
                                    '    output ≤ 2 * optimum := by\n'
                                    '  clear hhalf hconnection hcount\n  exact absurd cheat (by decide)')
            if name == 'M5-private-axiom':
                text = text.replace('    output ≤ 2 * optimum := by\n  omega',
                                    '    output ≤ 2 * optimum := by\n  exact absurd cheat (by decide)')
            if text.count(old) != 1:
                raise SystemExit('mutation anchor not unique: ' + name)
            path.write_text(text.replace(old, new))
        mutated = {f: hashlib.sha256((packet / f).read_bytes()).hexdigest()
                   for f in ['RCS128.lean', 'Controls.lean']}
        try:
            r = subprocess.run(['python3', '-I', str(packet / 'rebuild.py'), '--output',
                                str(case / 'build'), '--cache', str(args.cache), '--lean',
                                str(args.lean)], capture_output=True, text=True, env=env,
                               timeout=300, cwd=case)
            rcode, rerr = r.returncode, (r.stdout + r.stderr).strip().splitlines()
        except subprocess.TimeoutExpired:
            rcode, rerr = 124, ['TIMEOUT']
        receipt = case / 'build' / 'receipt.json'
        status = json.loads(receipt.read_text()).get('status') if receipt.exists() else None
        error = json.loads(receipt.read_text()).get('error') if receipt.exists() else None
        v = subprocess.run(['python3', '-I', str(packet / 'verify.py'), '--anchor', ANCHOR],
                           capture_output=True, text=True, cwd=case)
        logs = {p.name: p.read_text()[:400] for p in sorted((case / 'build').glob('*.log'))
                if p.stat().st_size} if (case / 'build').exists() else {}
        summary[name] = {'expectation': expectation, 'source_sha256_after_mutation': mutated, 'rebuild_exit': rcode,
                         'rebuild_last_line': rerr[-1] if rerr else '',
                         'receipt_status': status, 'receipt_error': error,
                         'nonempty_log_heads': logs,
                         'verify_exit': v.returncode,
                         'verify_output': (v.stdout + v.stderr).strip()}
        shutil.rmtree(packet)
        print(name, rcode, status, error, 'verify', v.returncode, flush=True)
    (out / 'summary.json').write_text(json.dumps(summary, indent=2, ensure_ascii=False) + '\n')


if __name__ == '__main__':
    main()
