"""Fresh extracted strict replay of the MathDB 366834 Lean packet.

Copies the two source files into an empty directory, scans for forbidden tokens, rebuilds with
`lean -j1 -DwarningAsError=true`, runs `leanchecker`, runs the all-local-declaration audit, and
writes replay/replay-result.json.  Each process: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB.
"""
from pathlib import Path
import os, sys, json, time, subprocess, resource, hashlib, re, shutil, datetime

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'formal'
R = ROOT / 'replay'
F = R / 'fresh'
BIN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
CACHE = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
FILES = ['CaterpillarCenter.lean', 'Audit.lean', 'OrdinalLine.lean', 'AuditOrdinal.lean']
PROOFS = ['CaterpillarCenter.lean', 'OrdinalLine.lean']
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

if R.exists():
    shutil.rmtree(R)
(R / 'logs').mkdir(parents=True)
F.mkdir()
for name in FILES:
    text = (SRC / name).read_text()
    body = re.sub(r'/-.*?-/', '', text, flags=re.S)
    body = re.sub(r'--.*', '', body)
    bad = re.findall(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by|extern)\b', body)
    if name in PROOFS:  # proof files; audit files name these words in diagnostics
        assert not bad, (name, bad)
    shutil.copy(SRC / name, F / name)

env = {'MALLOC_ARENA_MAX': '2', 'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1',
       'OPENBLAS_NUM_THREADS': '1', 'LANG': 'C.UTF-8',
       'PATH': str(BIN) + ':/usr/bin:/bin',
       'LEAN_PATH': ':'.join([str(F)] + [str(x / '.lake/build/lib/lean')
                                          for x in sorted(CACHE.iterdir()) if x.is_dir()])}

def limit():
    os.setsid()
    os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_AS, (64 << 30, 64 << 30))

def field(pid, key):
    s = Path(f'/proc/{pid}/status').read_text()
    return int(s.split(key + ':')[1].split()[0]) * 1024 if key + ':' in s else 0

rows = []
def run(label, cmd):
    t = time.monotonic(); peak = 0; anon = 0; reason = None
    with (R / 'logs' / f'{label}.log').open('w') as log:
        p = subprocess.Popen(cmd, cwd=F, stdout=log, stderr=subprocess.STDOUT, preexec_fn=limit, env=env)
        while p.poll() is None:
            try:
                peak = max(peak, field(p.pid, 'VmRSS')); anon = max(anon, field(p.pid, 'RssAnon'))
            except (FileNotFoundError, IndexError, ProcessLookupError):
                pass
            if anon > 6 << 30 or time.monotonic() - t > 140:
                reason = 'RSS or wall cap'; os.killpg(p.pid, 9); break
            time.sleep(.03)
        code = p.wait()
    row = dict(label=label, command=cmd, exit=code, wall_seconds=round(time.monotonic() - t, 3),
               peak_VmRSS_bytes=peak, peak_RssAnon_bytes=anon, cap_reason=reason)
    rows.append(row); print(label, code, flush=True)
    assert code == 0, (row, (R / 'logs' / f'{label}.log').read_text()[-3000:])
    return (R / 'logs' / f'{label}.log').read_text()

audits = {}
for mod, aud, ns, keys in [
        ('CaterpillarCenter', 'Audit', 'Caterpillar366834',
         ['not_caterpillarCenterConjecture', 'not_caterpillarCenterConjectureWeak', 'witness']),
        ('OrdinalLine', 'AuditOrdinal', 'OrdinalSpaces366371',
         ['not_majorizationConjecture', 'witness'])]:
    build_log = run('build-' + mod, [str(BIN / 'lean'), '-j1', '-DwarningAsError=true',
                                     '-o', mod + '.olean', mod + '.lean'])
    assert build_log.strip() == '', build_log
    run('leanchecker-' + mod, [str(BIN / 'leanchecker'), mod])
    audit = run('audit-' + mod, [str(BIN / 'lean'), '-j1', '-DwarningAsError=true', aud + '.lean'])
    assert 'sorryAx' not in audit
    locals_ = re.findall(r'LOCAL (\S+) AXIOMS \[([^\]]*)\]', audit)
    total = int(re.search(r'TOTAL_LOCAL (\d+)', audit).group(1))
    assert total == len(locals_) and total > 0
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for n, axs in locals_:
        assert set(a for a in axs.split(', ') if a) <= allowed, (n, axs)
    for ax in re.findall(r'depends on axioms: \[([^\]]*)\]', audit):
        assert set(ax.split(', ')) <= allowed
    names = {n for n, _ in locals_}
    for key in keys:
        assert f'{ns}.{key}' in names, key
    audits[mod] = dict(local_declarations_audited=total, endpoints=[f'{ns}.{k}' for k in keys],
                       olean_sha256=sha(F / (mod + '.olean')))

result = dict(
    status='PASS', utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    modules=audits,
    strict='lean -j1 -DwarningAsError=true; build logs empty', leanchecker='PASS (both modules)',
    allowed_axioms=['Classical.choice', 'Quot.sound', 'propext'],
    unsafe_or_partial_local_constants='none (audit fails on any)',
    source_sha256={n: sha(F / n) for n in FILES},
    lean_binary_sha256=sha(BIN / 'lean'), leanchecker_binary_sha256=sha(BIN / 'leanchecker'),
    mathlib_root_olean_sha256=sha(CACHE / 'mathlib/.lake/build/lib/lean/Mathlib.olean'),
    environment='Lean 4.34.1; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (cached oleans)',
    trust_limit='Prebuilt dependency oleans trusted as cached; no full upstream rebuild. Kernel decide '
                '(decide +kernel) used for finite checks; no native_decide/ofReduceBool. RSS is sampled, '
                'not cgroup-enforced.',
    runs=rows)
(R / 'replay-result.json').write_text(json.dumps(result, indent=2) + '\n')
print('Fresh strict replay, leanchecker and all-local-declaration audit PASS:', {m: a['local_declarations_audited'] for m, a in audits.items()})
