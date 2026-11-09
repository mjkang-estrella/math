#!/usr/bin/env python3
"""Portable fresh strict replay for MathDB 359279 (tableau minors, conj:k+4).

Adapted from root's tabminors-parent-check-r1/fixed2/run.py. Run it from a FRESH extraction
of the source-only ZIP:

    LEAN_BIN=/path/to/lean-4.34.1/bin LEAN_PACKAGES=/path/to/.lake/packages python3 -I replay.py

* Refuses to start if any .olean/.ilean/.c exists in the extraction (freshness).
* Verifies SOURCE-MANIFEST.json hashes, the Lean version/commit and the mathlib git pin.
* Strict sequential builds (-j1, -DwarningAsError=true) of TabMinors, AuditFull, Controls.
* leanchecker on each of the three modules.
* AuditFull: exactly 140 local declarations, none unsafe/partial, all with bodies,
  axioms within {propext, Classical.choice, Quot.sound}; not_conjecture's #print axioms.
* Negative controls NegControl1 and NegControl2 must FAIL with the expected errors.
* Caps per process: 2 CPUs, RLIMIT_CPU 120 s, wall 140 s, process-group RSS 6 GiB
  (sampled watchdog), MALLOC_ARENA_MAX=2, LEAN_NUM_THREADS=1. One process at a time.
* All outputs (oleans, logs/, receipts/, tmp/) stay inside the extraction.
"""
from pathlib import Path
import os, sys, json, subprocess, hashlib, resource, time, signal, re

W = Path(__file__).resolve().parent
os.chdir(W)
FRESH = [p for p in W.rglob('*') if p.suffix in ('.olean', '.ilean', '.c') or p.name.endswith('.olean.tmp')]
if FRESH:
    sys.exit('REFUSED: existing build products: ' + ', '.join(str(p.relative_to(W)) for p in FRESH[:5]))
for d in ['logs', 'receipts', 'tmp']: (W / d).mkdir(exist_ok=True)

LEAN_COMMIT = '5045d0056413266e57c625dcd7c365b10e377c52'
MATHLIB_COMMIT = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
ALLOWED = ['propext', 'Classical.choice', 'Quot.sound']
B = Path(os.environ['LEAN_BIN']).resolve()
P = Path(os.environ['LEAN_PACKAGES']).resolve()
FORMAL, NEG = W / 'formal', W / 'negative'

env = {k: v for k, v in os.environ.items() if not k.startswith(('LEAN', 'LAKE')) and k not in ('LD_PRELOAD',)}
libs = [str(p / '.lake/build/lib/lean') for p in sorted(P.iterdir()) if (p / '.lake/build/lib/lean').is_dir()]
env.update(LEAN_PATH=':'.join([str(FORMAL)] + libs), PATH=str(B) + ':/usr/bin:/bin', MALLOC_ARENA_MAX='2',
           LEAN_NUM_THREADS='1', TMPDIR=str(W / 'tmp'), PYTHONDONTWRITEBYTECODE='1')

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def limits():
    os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))

steps = []
def run(label, cmd, cwd, expected=0):
    start = time.monotonic(); peak = 0; killed = None
    with (W / 'logs' / f'{label}.log').open('w') as f:
        p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, start_new_session=True, preexec_fn=limits)
        while p.poll() is None:
            rss = 0
            for proc in Path('/proc').iterdir():
                if not proc.name.isdigit(): continue
                try:
                    if os.getpgid(int(proc.name)) != p.pid: continue
                    for line in (proc / 'status').read_text().splitlines():
                        if line.startswith('VmRSS:'): rss += int(line.split()[1])
                except (OSError, ValueError, ProcessLookupError): pass
            peak = max(peak, rss)
            if rss > 6 * 1024 * 1024 or time.monotonic() - start > 140:
                killed = 'RSS or wall cap'; os.killpg(p.pid, signal.SIGKILL); break
            time.sleep(0.05)
        p.wait()
    r = dict(label=label, command=[str(c) for c in cmd], cwd=str(Path(cwd).relative_to(W)) or '.', returncode=p.returncode,
             expected=expected, seconds=round(time.monotonic() - start, 1), peak_RSS_KiB=peak, killed=killed,
             cpu_limit_s=120, wall_limit_s=140, rss_cap_GiB=6, affinity_cpus=2, log_sha256=sha(W / 'logs' / f'{label}.log'))
    steps.append(r)
    (W / 'receipts' / f'{label}.json').write_text(json.dumps(r, indent=2) + '\n')
    if p.returncode != expected or killed:
        fail(f'{label}: returncode {p.returncode} (expected {expected}), killed={killed}; see logs/{label}.log')
    return (W / 'logs' / f'{label}.log').read_text(errors='replace')

def fail(msg):
    (W / 'receipts' / 'replay.json').write_text(json.dumps(dict(status='FAIL', reason=msg, steps=steps), indent=2) + '\n')
    sys.exit('FAIL: ' + msg)

# 1. Inputs and pins.
manifest = json.loads((W / 'SOURCE-MANIFEST.json').read_text())
for rel, h in manifest['files'].items():
    if sha(W / rel) != h: fail(f'hash mismatch {rel}')
for rel in ['formal/TabMinors.lean', 'formal/Controls.lean', 'negative/NegControl1.lean', 'negative/NegControl2.lean']:
    if re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern|opaque)\b', (W / rel).read_text()):
        fail(f'forbidden token in {rel}')
v = run('version', [str(B / 'lean'), '--version'], W)
if '4.34.1' not in v or LEAN_COMMIT not in v: fail('Lean version/commit pin mismatch')
head = P / 'mathlib/.git/HEAD'
mathlib_head = head.read_text().strip() if head.is_file() else None
if mathlib_head is not None and mathlib_head != MATHLIB_COMMIT: fail(f'mathlib pin mismatch {mathlib_head}')

# 2. Strict builds and leanchecker.
logs = {}
for m in ['TabMinors', 'AuditFull', 'Controls']:
    logs[m] = run('build-' + m, [str(B / 'lean'), '-j1', '-DwarningAsError=true', '-o', m + '.olean', m + '.lean'], FORMAL)
for m in ['TabMinors', 'AuditFull', 'Controls']:
    run('check-' + m, [str(B / 'leanchecker'), m], FORMAL)

# 3. Axiom and full-flag audit.
want = "'TabMinors.not_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]"
if want not in logs['TabMinors']: fail('not_conjecture axiom line missing')
a = logs['AuditFull']
decls = [l for l in a.splitlines() if l.startswith('DECL|')]
if 'AUDITED_LOCAL_DECLARATIONS|140' not in a or len(decls) != 140: fail(f'AuditFull count {len(decls)}')
for l in decls:
    f = l.split('|')
    if f[3] != 'false' or f[5] != 'false' or f[7] != 'true': fail('bad flags: ' + l)
    axs = [x.strip() for x in f[9].strip('[]').split(',') if x.strip()]
    if any(x not in ALLOWED for x in axs): fail('disallowed axiom: ' + l)
if not any('TabMinors.not_conjecture|' in l for l in decls): fail('not_conjecture not audited')

# 4. Negative controls must fail.
n1 = run('negative-NegControl1', [str(B / 'lean'), '-j1', '-DwarningAsError=true', 'NegControl1.lean'], NEG, expected=1)
if 'error' not in n1 or 'is false' not in n1: fail('NegControl1 failed for an unexpected reason')
n2 = run('negative-NegControl2', [str(B / 'lean'), '-j1', '-DwarningAsError=true', 'NegControl2.lean'], NEG, expected=1)
if 'error' not in n2 or not ('type mismatch' in n2 or 'is false' in n2): fail('NegControl2 failed for an unexpected reason')

# 5. Freshness refusal self-test (must refuse now that oleans exist).
p = subprocess.run([sys.executable, '-I', str(W / 'replay.py')], env=env, capture_output=True, text=True, timeout=60)
(W / 'logs' / 'freshness-negative.log').write_text(p.stdout + p.stderr)
if p.returncode == 0 or 'REFUSED' not in p.stderr: fail('freshness refusal self-test')

res = dict(status='PASS', mathdb_id='359279', endpoint='TabMinors.not_conjecture : ¬ TabMinors.Conjecture',
           lean_commit=LEAN_COMMIT, mathlib_commit=MATHLIB_COMMIT, mathlib_git_head_checked=mathlib_head is not None,
           modules=['TabMinors', 'AuditFull', 'Controls'], leanchecker='OK x3', audited_declarations=140,
           trusted_axioms=ALLOWED, negative_controls_rejected=['NegControl1', 'NegControl2'], freshness_refusal='PASS',
           source_sha256={k: v for k, v in manifest['files'].items()},
           olean_sha256={m: sha(FORMAL / (m + '.olean')) for m in ['TabMinors', 'AuditFull', 'Controls']}, steps=steps)
(W / 'receipts' / 'replay.json').write_text(json.dumps(res, indent=2) + '\n')
print('PASS: strict replay of TabMinors/AuditFull/Controls, leanchecker x3, 140-declaration audit, 2 negative controls rejected')
