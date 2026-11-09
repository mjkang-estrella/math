"""Portable replay driver for the MathDB 378395 packet (DRAFT, zero accepted credit).

Usage (from a FRESH extraction of source-only-packet.zip):
    LEAN_BIN=/path/to/lean-4.34.1/bin LEAN_PACKAGES=/path/to/.lake/packages python3 -I replay.py

Checks pinned binary hashes and the source manifest, refuses pre-existing oleans, builds the
literal module proof/MathDB378395.lean with -j1 -DwarningAsError=true, runs leanchecker, the
full local-declaration audit, the sanity supplement, the negative controls and the exact
diagnostic.  Every call is limited to <= 2 CPUs, CPU 120 s, wall 140 s, AS 64 GiB,
MALLOC_ARENA_MAX=2, and a 6 GiB guard on the sampled (50 ms) private resident set
(RssAnon + RssShmem) of the process group.  The imported Mathlib .olean files are mmapped
read-only, so TOTAL VmRSS (which counts those clean file-backed pages) can be large; it is
sampled and reported but is not the kill criterion.  When a user systemd manager is available
(and REPLAY_NO_SYSTEMD is unset) each call also runs in a transient scope with MemoryMax=6G,
MemorySwapMax=0 and CPUQuota=200%.  Receipts go to replay-receipts/.  The driver creates only
replay-receipts/, controls/ and proof/MathDB378395.olean (+ .ilean) inside this extraction and
deletes nothing.
"""
import hashlib, json, os, pathlib, re, resource, shutil, signal, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent
OUT = ROOT / 'replay-receipts'
PROOF = ROOT / 'proof'
CTRL = ROOT / 'controls'
BIN = pathlib.Path(os.environ['LEAN_BIN']).resolve()
PACK = pathlib.Path(os.environ['LEAN_PACKAGES']).resolve()
LIBS = [str(p / '.lake/build/lib/lean') for p in sorted(PACK.iterdir()) if (p / '.lake/build/lib/lean').is_dir()]
ENV = {'HOME': os.environ['HOME'], 'PATH': str(BIN) + ':/usr/bin:/bin', 'LANG': 'C.UTF-8',
       'LEAN_PATH': ':'.join([str(PROOF), str(CTRL)] + LIBS), 'LEAN_NUM_THREADS': '1', 'MALLOC_ARENA_MAX': '2'}
CPUS = sorted(os.sched_getaffinity(0))[:2]
PAGE = os.sysconf('SC_PAGE_SIZE')
RSS_CAP, WALL_CAP, CPU_CAP, AS_CAP = 6 * 1024 ** 3, 140, 120, 64 * 1024 ** 3
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
INVENTORY = 134
ENDPOINTS = ('MathDB378395.Main.collapsing_conjecture_false', 'MathDB378395.Main.exists_noncollapsible_facet')


def group_rss(pgid):
    """Return (total VmRSS, private RssAnon+RssShmem) in bytes over the process group."""
    total = private = 0
    for q in pathlib.Path('/proc').glob('[0-9]*'):
        try:
            s = (q / 'stat').read_text()
            fields = s[s.rindex(')') + 2:].split()      # fields after "pid (comm)"
            if int(fields[2]) != pgid:                   # pgrp
                continue
            total += int(fields[21]) * PAGE              # rss pages
            for line in (q / 'status').read_text().splitlines():
                if line.startswith(('RssAnon:', 'RssShmem:')):
                    private += int(line.split()[1]) * 1024
        except (OSError, ValueError, IndexError):
            pass
    return total, private


def systemd_prefix():
    if os.environ.get('REPLAY_NO_SYSTEMD') or not shutil.which('systemd-run') or 'XDG_RUNTIME_DIR' not in os.environ:
        return []
    pre = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=6G', '-p', 'MemorySwapMax=0', '-p', 'CPUQuota=200%']
    probe = subprocess.run(pre + ['/usr/bin/true'], capture_output=True, timeout=60)
    return pre if probe.returncode == 0 else []


SCOPE = systemd_prefix()
if SCOPE:
    for k in ('XDG_RUNTIME_DIR', 'DBUS_SESSION_BUS_ADDRESS'):
        if k in os.environ:
            ENV[k] = os.environ[k]


def run(label, cmd, cwd):
    def setup():
        os.setsid()
        os.sched_setaffinity(0, CPUS)
        resource.setrlimit(resource.RLIMIT_CPU, (CPU_CAP, CPU_CAP))
        resource.setrlimit(resource.RLIMIT_AS, (AS_CAP, AS_CAP))
    start, peak, peak_priv, why = time.monotonic(), 0, 0, None
    full = SCOPE + cmd
    with (OUT / (label + '.log')).open('w') as f:
        p = subprocess.Popen(full, cwd=cwd, env=ENV, stdout=f, stderr=subprocess.STDOUT, preexec_fn=setup)
        while p.poll() is None:
            rss, priv = group_rss(p.pid)
            peak, peak_priv = max(peak, rss), max(peak_priv, priv)
            if priv > RSS_CAP or time.monotonic() - start > WALL_CAP:
                why = 'RSS' if priv > RSS_CAP else 'wall'
                os.killpg(p.pid, signal.SIGKILL)
                break
            time.sleep(0.05)
        p.wait()
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    r = {'label': label, 'command': full, 'cwd': str(cwd), 'environment': ENV, 'cpus': CPUS,
         'cpu_limit_s': CPU_CAP, 'wall_limit_s': WALL_CAP, 'AS_bytes': AS_CAP,
         'private_RSS_guard_bytes': RSS_CAP, 'systemd_scope': bool(SCOPE), 'sample_seconds': 0.05,
         'peak_sampled_private_rss_bytes': peak_priv, 'peak_sampled_total_vmrss_bytes': peak,
         'wall_seconds': round(time.monotonic() - start, 3), 'exit': p.returncode, 'killed_reason': why,
         'children_cpu_seconds_cumulative': round(ru.ru_utime + ru.ru_stime, 2)}
    (OUT / (label + '.receipt.json')).write_text(json.dumps(r, indent=2))
    print(label, 'exit', p.returncode, 'wall', r['wall_seconds'], 'peak private', peak_priv, 'peak total', peak, flush=True)
    return r


def log(label):
    return (OUT / (label + '.log')).read_text(errors='replace')


def lean(*args):
    return [str(BIN / 'lean'), '-j1', '-DwarningAsError=true', *args]


def error_lines(text, fname):
    return [int(m) for m in re.findall(re.escape(fname) + r':(\d+):\d+: error', text)]


def main():
    pins = json.loads((ROOT / 'pins.json').read_text())
    for n in ('lean', 'leanchecker'):
        assert hashlib.sha256((BIN / n).read_bytes()).hexdigest() == pins['binaries'][n], 'binary hash ' + n
    # Pinned source revisions are metadata checks; cached oleans remain trusted inputs.
    for pkg in pins['dependency_manifest']['packages']:
        gd = PACK / pkg['name'] / '.git'
        assert gd.is_dir(), 'expected cache git metadata directory'
        head = (gd / 'HEAD').read_text().strip()
        if head.startswith('ref: '):
            ref = head[5:]
            if (gd / ref).is_file():
                head = (gd / ref).read_text().strip()
            else:
                records = (gd / 'packed-refs').read_text().splitlines()
                head = next(line.split()[0] for line in records if line.endswith(' ' + ref))
        assert head == pkg['rev'], 'cache source revision ' + pkg['name']
    manifest = json.loads((ROOT / 'source-manifest.json').read_text())
    for name, digest in manifest.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, 'manifest ' + name
    assert manifest['proof/MathDB378395.lean'] == pins['module_sha256'], 'literal module hash'
    assert not OUT.exists(), 'replay-receipts/ exists: use a fresh extraction'
    assert not CTRL.exists(), 'controls/ exists: use a fresh extraction'
    assert not list(ROOT.rglob('*.olean')), 'pre-existing .olean found: use a fresh extraction'
    OUT.mkdir()
    CTRL.mkdir()
    res = {}
    v = run('lean-version', [str(BIN / 'lean'), '--version'], PROOF)
    assert v['exit'] == 0 and pins['lean_commit_expected'] in log('lean-version')

    # 1. strict -j1 build of the literal module (empty log), then independent kernel re-check.
    assert run('build-MathDB378395', lean('-o', 'MathDB378395.olean', '-i', 'MathDB378395.ilean', 'MathDB378395.lean'), PROOF)['exit'] == 0
    assert log('build-MathDB378395').strip() == '', 'strict build produced messages'
    assert run('kernel-MathDB378395', [str(BIN / 'leanchecker'), 'MathDB378395'], PROOF)['exit'] == 0

    # 2. full local-declaration audit.
    assert run('audit', lean('ReviewAudit.lean'), PROOF)['exit'] == 0
    a = log('audit')
    decls = re.findall(r'DECL (\S+) ORIGIN some \(MathDB378395\) KIND (\S+) UNSAFE false PARTIAL false BODY (true|false)', a)
    axioms = re.findall(r'TRANSITIVE_AXIOMS (\S+) \[(.*?)\]', a)
    names = [d[0] for d in decls]
    assert f'TOTAL {INVENTORY}' in a and len(decls) == INVENTORY and len(set(names)) == INVENTORY and len(axioms) == INVENTORY
    assert a.count('FULL_TYPE ') == INVENTORY
    for n, kind, body in decls:
        assert kind in ('def', 'theorem', 'inductive', 'ctor', 'recursor'), (n, kind)
        assert body == 'true' or kind in ('inductive', 'ctor', 'recursor'), (n, kind)
    for n, axs in axioms:
        assert set(x.strip() for x in axs.split(',') if x.strip()) <= ALLOWED, n
    for endpoint in ENDPOINTS:
        assert endpoint in names
    kinds = {}
    for _, kind, _ in decls:
        kinds[kind] = kinds.get(kind, 0) + 1
    res['declarations'] = sorted(names)
    res['kinds'] = kinds

    # 3. sanity supplement: literal statements, endpoint types, non-vacuity, endpoint axioms.
    assert run('sanity', lean('ReviewSanity.lean'), PROOF)['exit'] == 0
    s = log('sanity')
    printed = re.findall(r"'(MathDB378395\.Main\.\w+)' depends on axioms: \[(.*?)\]", s)
    assert sorted(p[0] for p in printed) == sorted(ENDPOINTS), printed
    for _, axs in printed:
        assert set(x.strip() for x in axs.split(',')) <= ALLOWED

    # 4. controls.
    src = (PROOF / 'MathDB378395.lean').read_text(encoding='utf-8')
    anchor = 'theorem ell_nonneg : ∀ c : Cell 4 4 5, 0 ≤ onCol ellZ c := by decide +kernel\n'
    assert src.count(anchor) == 1
    prefix = src[:src.index(anchor) + len(anchor)] + 'end MathDB378395.Cert\n'
    ell_block = src[src.index('def ellZ : Margin 4 4 5 → ℤ :='):src.index(anchor)]
    row = '![0, 0, 0, 1]'
    assert ell_block.count(row) == 1
    perturbed = prefix.replace(ell_block, ell_block.replace(row, '![0, 0, 0, -2]'))
    assert perturbed != prefix
    nn_line = prefix[:prefix.index(anchor)].count('\n') + 1
    head = 'import MathDB378395\nset_option warningAsError true\n'
    controls = {
        'control-prefix-verbatim': (prefix, 0, None),
        'negative-perturbed-table': (perturbed, 1, None),
        'negative-wrong-endpoint': (head + 'example : MathDB378395.CollapsingConjecture := MathDB378395.Main.collapsing_conjecture_false\n', 1, 'type mismatch'),
        'negative-sorry': (head + 'theorem s : MathDB378395.CollapsingConjecture := by sorry\n', 1, 'sorry'),
        'negative-forbidden-axiom': (head + 'axiom cheat : MathDB378395.CollapsingConjecture\n'
                                     'theorem uses_cheat : MathDB378395.CollapsingConjecture := cheat\n'
                                     'open Lean Elab Command in\nrun_cmd do\n let axs ← Lean.collectAxioms `uses_cheat\n'
                                     ' for ax in axs do\n  unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do\n'
                                     '   throwError "forbidden axiom {ax}"\n', 1, 'forbidden axiom cheat'),
    }
    for label, (text, code, needle) in controls.items():
        fname = label.replace('-', '_') + '.lean'
        (CTRL / fname).write_text(text, encoding='utf-8')
        r = run(label, lean(fname), CTRL)
        assert r['exit'] == code, label
        if needle:
            assert needle.lower() in log(label).lower(), label
        if code == 0:
            assert log(label).strip() == '', label
    pe = error_lines(log('negative-perturbed-table'), 'negative_perturbed_table.lean')
    assert pe and set(pe) == {nn_line}, (pe, nn_line)
    res['perturbed_table_error_lines'] = pe
    (CTRL / 'BadCertificate.olean').write_bytes(b'Deliberately invalid Lean certificate\n')
    r = run('negative-malformed-olean', [str(BIN / 'leanchecker'), 'BadCertificate'], CTRL)
    assert r['exit'] != 0

    # 5. exact diagnostic (corroboration only).
    assert run('diagnostic', [sys.executable, '-I', str(ROOT / 'diagnostic.py'), str(OUT / 'diagnostic.json')], ROOT)['exit'] == 0
    diag = json.loads((OUT / 'diagnostic.json').read_text())
    assert diag['status'] == 'PASS' and diag['result']['rank_tight'] == 43 and diag['result']['rank_all'] == 44

    receipts = [json.loads(p.read_text()) for p in sorted(OUT.glob('*.receipt.json'))]
    assert all(r['killed_reason'] is None for r in receipts)
    outputs = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted(list(PROOF.glob('*.olean')) + list(PROOF.glob('*.ilean')) + list(CTRL.glob('*')))}
    (OUT / 'all-receipts.json').write_text(json.dumps(receipts, indent=2))
    (OUT / 'output-hashes.json').write_text(json.dumps(outputs, indent=2))
    result = {'status': 'PASS', 'mathdb_id': 378395, 'strict_builds': 1, 'leanchecker': 1,
              'literal_module_sha256': manifest['proof/MathDB378395.lean'],
              'audited_local_declarations': INVENTORY, 'declaration_kinds': kinds,
              'allowed_axioms': sorted(ALLOWED), 'negative_controls_rejected': 5,
              'positive_harness_controls': 1, 'diagnostic': 'PASS (corroboration only)',
              'systemd_scope_MemoryMax_6G': bool(SCOPE),
              'max_sampled_private_rss_bytes': max(r['peak_sampled_private_rss_bytes'] for r in receipts),
              'max_sampled_total_vmrss_bytes': max(r['peak_sampled_total_vmrss_bytes'] for r in receipts),
              'max_wall_seconds': max(r['wall_seconds'] for r in receipts), 'accepted_credit': 0,
              'endpoints': list(ENDPOINTS), 'details': res}
    (OUT / 'result.json').write_text(json.dumps(result, indent=2))
    print('REPLAY PASS')


if __name__ == '__main__':
    main()
