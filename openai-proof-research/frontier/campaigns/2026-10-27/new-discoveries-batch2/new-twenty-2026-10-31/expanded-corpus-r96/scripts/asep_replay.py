"""368807 Lean packet: fresh extracted strict rebuild against the pinned prebuilt mathlib cache.

Copies lean/ASEP*.lean into a new empty directory, clears inherited Lean settings, compiles every
module in dependency order with -DwarningAsError=true (each under rsscap.py: RSS 6 GiB, CPU 120 s,
wall 140 s, 2 threads), runs leanchecker on every module, scans sources for forbidden constructs and
audits the transitive axioms printed by ASEPMain.  Writes <out>/result.json.
usage: asep_replay.py OUTDIR"""
import sys, os, json, hashlib, pathlib, re, shutil, subprocess, time
L0 = pathlib.Path(__file__).resolve().parents[1]
out = pathlib.Path(sys.argv[1]).resolve()
assert not out.exists(), 'output directory must be new'
out.mkdir(parents=True)
LEAN = '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
CHECKER = '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker'
PKG = pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
manifest = json.loads((PKG.parent.parent / 'lake-manifest.json').read_text())
deps = []
for p in manifest['packages']:
    d = PKG / p['name']; meta = d / '.git'
    if meta.is_file(): meta = (d / meta.read_text().strip().removeprefix('gitdir: ')).resolve()
    head = (meta / 'HEAD').read_text().strip()
    if head.startswith('ref: '):
        rf = meta / head[5:]
        head = rf.read_text().strip() if rf.exists() else next(x.split()[0] for x in (meta / 'packed-refs').read_text().splitlines() if x.endswith(' ' + head[5:]))
    assert head == p['rev'], (p['name'], head, p['rev'])
    lib = d / '.lake/build/lib/lean'
    deps.append({'name': p['name'], 'rev': head, 'library': str(lib), 'present': lib.is_dir()})
order = ['ASEPData', 'ASEPCheck', 'ASEPCover'] + [f'ASEPCerts{m}' for m in range(12)] + ['ASEPDefs', 'ASEPSound', 'ASEPVertex', 'ASEPBridge', 'ASEPMain', 'ASEPArcs']
src = out / 'src'; src.mkdir(); build = out / 'build'; build.mkdir()
hashes = {}
for m in order:
    shutil.copyfile(L0 / 'lean' / f'{m}.lean', src / f'{m}.lean')
    hashes[m] = hashlib.sha256((src / f'{m}.lean').read_bytes()).hexdigest()
forbidden = re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by|extern)\b')
scan = {m: [l for l in (src / f'{m}.lean').read_text().splitlines() if forbidden.search(l) and not l.strip().startswith('--')] for m in order}
env = {k: v for k, v in os.environ.items() if k in ('PATH', 'HOME', 'TMPDIR', 'LANG')}
env['LEAN_PATH'] = os.pathsep.join([x['library'] for x in deps if x['present']] + [str(build)])
env['OMP_NUM_THREADS'] = '2'
env['PATH'] = str(pathlib.Path(LEAN).parent) + os.pathsep + env.get('PATH', '/usr/bin:/bin')
steps = []
for m in order:
    t = time.monotonic()
    r = subprocess.run([sys.executable, str(L0 / 'scripts/rsscap.py'), '6144', '140', '120', '--', LEAN, '-j2', '-DwarningAsError=true',
                        '-o', str(build / f'{m}.olean'), str(src / f'{m}.lean')], cwd=src, env=env, text=True, capture_output=True)
    (out / f'{m}.stdout.log').write_text(r.stdout); (out / f'{m}.stderr.log').write_text(r.stderr)
    steps.append({'module': m, 'exit': r.returncode, 'elapsed_s': round(time.monotonic() - t, 2), 'rsscap': r.stderr.strip().splitlines()[-1] if r.stderr.strip() else None})
    if r.returncode != 0: break
checks = []
if all(s['exit'] == 0 for s in steps) and len(steps) == len(order):
    for m in order:
        r = subprocess.run([sys.executable, str(L0 / 'scripts/rsscap.py'), '6144', '140', '120', '--', CHECKER, m], cwd=build, env=env, text=True, capture_output=True)
        (out / f'{m}.leanchecker.log').write_text(r.stdout + r.stderr)
        checks.append({'module': m, 'exit': r.returncode, 'rsscap': r.stderr.strip().splitlines()[-1] if r.stderr.strip() else None})
main_out = ''.join((out / f'{m}.stdout.log').read_text() for m in ('ASEPMain', 'ASEPArcs') if (out / f'{m}.stdout.log').exists())
axioms = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", main_out)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
ax_ok = len(axioms) == 5 and all(set(a.strip() for a in names.split(',')) <= allowed for _, names in axioms)
version = subprocess.run([LEAN, '--version'], text=True, capture_output=True).stdout.strip()
res = {'lean_version': version, 'dependencies': deps, 'module_order': order, 'source_sha256': hashes, 'forbidden_scan': scan,
       'forbidden_clean': all(not v for v in scan.values()), 'build_steps': steps, 'leanchecker': checks,
       'axioms': axioms, 'axiom_audit_pass': ax_ok,
       'all_ok': ax_ok and all(not v for v in scan.values()) and len(steps) == len(order) and all(s['exit'] == 0 for s in steps)
                 and len(checks) == len(order) and all(c['exit'] == 0 for c in checks),
       'scope': 'fresh copy of the packet sources rebuilt against pinned prebuilt dependency oleans; no upstream mathlib rebuild'}
(out / 'result.json').write_text(json.dumps(res, indent=2) + '\n')
print(json.dumps({k: res[k] for k in ('forbidden_clean', 'axiom_audit_pass', 'all_ok')}), json.dumps(steps[-1]), len(checks))
