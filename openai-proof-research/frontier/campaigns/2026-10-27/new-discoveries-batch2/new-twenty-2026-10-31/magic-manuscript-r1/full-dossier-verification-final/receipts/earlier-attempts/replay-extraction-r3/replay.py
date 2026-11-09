"""Portable offline Magic381805 replay; fresh extraction only. See REPRODUCE.md."""
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
INVENTORY = 37
ENDPOINTS = ('Magic381805.source_refutation', 'Magic381805.strength_le')


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
        assert hashlib.sha256((BIN/n).read_bytes()).hexdigest() == pins['binaries'][n], n
    # Resolve immutable revision metadata without invoking git or modifying the cache.
    def head(pkg):
        g=PACK/pkg/'.git'
        if g.is_file():
            g=(PACK/pkg/g.read_text().strip().split(': ',1)[1]).resolve()
        h=(g/'HEAD').read_text().strip()
        if h.startswith('ref: '):
            ref=h[5:]; f=g/ref
            if f.exists(): return f.read_text().strip()
            return next(l.split()[0] for l in (g/'packed-refs').read_text().splitlines() if l.endswith(' '+ref))
        return h
    for pkg, info in pins['package_heads_read_directly'].items():
        assert head(pkg) == info['HEAD_file'], 'package revision '+pkg
    manifest=json.loads((ROOT/'source-manifest.json').read_text())
    for name,digest in manifest.items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest, name
    assert manifest['proof/Magic.lean']==pins['magic_sha256']
    assert not OUT.exists() and not CTRL.exists(), 'fresh extraction required'
    assert not list(ROOT.rglob('*.olean')), 'pre-existing olean refused'
    OUT.mkdir(); CTRL.mkdir()
    assert run('lean-version',[str(BIN/'lean'),'--version'],PROOF)['exit']==0
    assert pins['lean_commit_expected'] in log('lean-version')
    assert run('build-Magic',lean('-o','Magic.olean','-i','Magic.ilean','Magic.lean'),PROOF)['exit']==0
    assert not log('build-Magic').strip()
    assert run('leanchecker',[str(BIN/'leanchecker'),'Magic'],PROOF)['exit']==0
    assert run('audit',lean('ReviewAudit.lean'),PROOF)['exit']==0
    a=log('audit')
    decls=re.findall(r'DECL\|([^|\s]+)\|unsafe=false\|partial=false\|body=true\|axioms=\[(.*?)\]',a,re.S)
    assert len(decls)==37 and len({n for n,_ in decls})==37 and 'COUNT|37' in a
    assert a.count('FULL_TYPE|')==37
    for n,axs in decls:
        assert set(x.strip() for x in axs.split(',') if x.strip()) <= ALLOWED,n
    assert all(n in dict(decls) for n in ENDPOINTS)
    src=(PROOF/'Magic.lean').read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool)\b',src)
    head='import Magic\nset_option warningAsError true\nopen Magic381805\n'
    controls={
      'positive-sanity':(head+'example : vertexLabel 6 = 1 := by decide\nexample : ¬G.Adj 0 2 := by decide\nexample : ¬IsSuperEdgeMagic G 11 11 27 labelEquiv := by unfold IsSuperEdgeMagic; decide\n',0,None),
      'negative-wrong-constant':(head+'example : IsSuperEdgeMagic G 11 11 27 labelEquiv := by unfold IsSuperEdgeMagic; decide\n',1,'is false'),
      'negative-wrong-endpoint':(head+'example : SourceConjecture := source_refutation\n',1,'type mismatch'),
      'negative-sorry':(head+'example : SourceConjecture := by sorry\n',1,'sorry'),
      'negative-duplicate-label':(head+'def bad : V → ℕ := ![3,3,4,5,8,6,1,7,9,10,11]\nexample : Function.Injective bad := by decide\n',1,'is false'),
      'negative-forbidden-axiom':(head+'axiom cheat : SourceConjecture\ntheorem uses_cheat : SourceConjecture := cheat\nopen Lean Elab Command in\nrun_cmd do\n let axs ← Lean.collectAxioms `uses_cheat\n for ax in axs do\n  unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do\n   throwError "forbidden axiom {ax}"\n',1,'forbidden axiom cheat')}
    for label,(txt,code,needle) in controls.items():
        name=label.replace('-','_')+'.lean'; (CTRL/name).write_text(txt)
        assert run(label,lean(name),CTRL)['exit']==code,label
        if needle: assert needle in log(label),label
        else: assert not log(label).strip()
    (CTRL/'BadCertificate.olean').write_bytes(b'Invalid Lean certificate\n')
    assert run('negative-malformed-olean',[str(BIN/'leanchecker'),'BadCertificate'],CTRL)['exit']!=0
    assert 'header' in log('negative-malformed-olean').lower()
    receipts=[json.loads(p.read_text()) for p in sorted(OUT.glob('*.receipt.json'))]
    assert all(r['killed_reason'] is None for r in receipts)
    result={'status':'PASS','mathdb_id':381805,'literal_module_sha256':pins['magic_sha256'],
      'strict_build':'-j1 -DwarningAsError=true','leanchecker':'PASS','full_module_declarations':37,
      'allowed_axioms':sorted(ALLOWED),'negative_controls_rejected':6,'positive_sanity':'PASS',
      'ordinary_exact_minimum_formalized':False,'endpoints':list(ENDPOINTS),'accepted_credit':0,
      'systemd_scope_MemoryMax_6G':bool(SCOPE),'declarations':[n for n,_ in decls],
      'max_private_rss_bytes':max(r['peak_sampled_private_rss_bytes'] for r in receipts),
      'max_total_vmrss_bytes':max(r['peak_sampled_total_vmrss_bytes'] for r in receipts),
      'max_wall_seconds':max(r['wall_seconds'] for r in receipts)}
    (OUT/'result.json').write_text(json.dumps(result,indent=2))
    (OUT/'all-receipts.json').write_text(json.dumps(receipts,indent=2))
    print('REPLAY PASS',flush=True)
if __name__=='__main__': main()
