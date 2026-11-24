#!/usr/bin/env python3
"""Root replay, parallel: same checks as root-replay.py (extract modules from LEAN-SOURCE-APPENDIX.md of an author packet into a
fresh dir, byte-compare with the author's src/, rebuild, kernel-check, collect axioms, scan for forbidden tokens), but modules
whose local imports are done run concurrently, one pinned core each.
Checkpointing variant for very large packets (writes ROOT-REPLAY.json every 50 modules).
Usage: root-replay-parallel-ckpt.py AUTHOR_PACKET_DIR REPLAY_DIR CPUS(e.g. 0,1,2,3) [resume]"""
import re, sys, hashlib, shutil, subprocess, json, os
from pathlib import Path
A = Path(sys.argv[1]).resolve(); R = Path(sys.argv[2]).resolve(); cpus = sys.argv[3].split(',')
RESUME = len(sys.argv) > 4 and sys.argv[4] == 'resume'
prior = {}
if RESUME:
    # resume a replay that was cut short by the runner's wall-time guard: keep modules that already passed, rerun the rest
    prior = json.loads((R / 'ROOT-REPLAY.json').read_text())['runs']
    prior = {m: r for m, r in prior.items() if r['compile'] == 0 and r['kernel'] == 0}
else:
    assert not R.exists(), 'replay dir exists'
    (R / 'src').mkdir(parents=True); (R / 'build').mkdir(); (R / 'cache').mkdir()
for f in ('run_lean_32g.py', 'formal_command.py', 'check32.sh', 'checker32.sh', 'write_lane.py', 'PINS.json'):
    shutil.copy2(A / f, R / f)
for f in ('check32.sh', 'checker32.sh'): os.chmod(R / f, 0o755)
HEAP = os.environ.get('ROOT_REPLAY_HEAP_MB')
if HEAP:
    # root option: raise Lean's -M heap threshold for modules that exceed the default 3500 MB (a resource limit, not a soundness matter)
    fc = (R / 'formal_command.py').read_text(); assert "'-M3500'" in fc
    (R / 'formal_command.py').write_text(fc.replace("'-M3500'", f"'-M{int(HEAP)}'"))
t = (A / 'LEAN-SOURCE-APPENDIX.md').read_text()
blocks = re.findall(r'^#+[^\n`A-Za-z]*`?([A-Za-z][A-Za-z0-9_]*)(?:\.lean)?`?[^\n]*\n+```lean\n(.*?)\n```[ \t]*$', t, flags=re.S | re.M)
order, bad, deps = [], [], {}
for name, body in blocks:
    body += '\n'; order.append(name)
    tgt = R / 'src' / f'{name}.lean'
    if RESUME and name in prior: assert tgt.read_text() == body, f'{name}: extracted source changed since the first run'
    else: tgt.write_text(body)
    src = A / 'src' / f'{name}.lean'
    if not src.exists() or hashlib.sha256(body.encode()).hexdigest() != hashlib.sha256(src.read_bytes()).hexdigest(): bad.append(name)
names = set(order)
for name, body in blocks:
    deps[name] = set(m for m in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z][A-Za-z0-9_.]*)', body, flags=re.M) if m in names)
missing = sorted(set(p.stem for p in (A / 'src').glob('*.lean')) - names)
GUARD = os.environ.get('ROOT_REPLAY_RSS_GUARD_GIB')
if GUARD:
    # root option: raise the runner's group RSS guard (default 6 GiB) for the few modules that need it; the 32 GiB address-space limit stays
    rl = (R / 'run_lean_32g.py').read_text(); assert rl.count('6*1024**3') == 3
    (R / 'run_lean_32g.py').write_text(rl.replace('6*1024**3', f'{int(GUARD)}*1024**3'))
res = {'heap_mb_override': HEAP, 'rss_guard_gib_override': GUARD, 'modules': order, 'appendix_vs_author_src_mismatch': bad, 'author_src_not_in_appendix': missing, 'runs': {}, 'parallel': len(cpus)}
done = set(prior); started = set(prior); res['runs'].update(prior); res['resumed_from'] = sorted(prior)
import time as _t
SUF = ('-resume' + _t.strftime('%H%M%S')) if RESUME else ''
def run(m, cpu):
    c = subprocess.run(['taskset', '-c', cpu, './check32.sh', m, f'root-compile-{m}{SUF}'], cwd=R, capture_output=True, text=True)
    (R / f'root-compile-{m}{SUF}.console.txt').write_text(c.stdout + c.stderr)
    k = subprocess.run(['taskset', '-c', cpu, './checker32.sh', m, f'root-kernel-{m}{SUF}'], cwd=R, capture_output=True, text=True)
    (R / f'root-kernel-{m}{SUF}.console.txt').write_text(k.stdout + k.stderr)
    same = None
    ao, ro = A / 'build' / f'{m}.olean', R / 'build' / f'{m}.olean'
    if ao.exists() and ro.exists(): same = hashlib.sha256(ao.read_bytes()).hexdigest() == hashlib.sha256(ro.read_bytes()).hexdigest()
    ax = sorted(set(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", c.stdout)))
    return {'compile': c.returncode, 'kernel': k.returncode, 'olean_matches_author': same, 'axioms': ax}
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
failed = set(); free = list(cpus); running = {}; ncomp = 0
with ThreadPoolExecutor(max_workers=len(cpus)) as ex:
    while True:
        ready = [m for m in order if m not in started and deps[m] <= done]
        while ready and free:
            m = ready.pop(0); cpu = free.pop(); started.add(m)
            running[ex.submit(run, m, cpu)] = (m, cpu)
        if not running: break
        fin, _ = wait(list(running), return_when=FIRST_COMPLETED)
        for f in fin:
            m, cpu = running.pop(f); r = f.result(); res['runs'][m] = r; free.append(cpu)
            (done if r['compile'] == 0 and r['kernel'] == 0 else failed).add(m)
            ncomp += 1
            if ncomp % 50 == 0:
                # checkpoint so that a cut-off run can be resumed
                tmp = R / 'ROOT-REPLAY.json.tmp'; tmp.write_text(json.dumps(res)); os.replace(tmp, R / 'ROOT-REPLAY.json')
                print(f'checkpoint: {len(done)} ok, {len(failed)} failed of {len(order)}', flush=True)
ok = len(done) == len(order)
res['not_run'] = [m for m in order if m not in res['runs']]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
res['axioms_ok'] = all(set(x.strip() for x in a.split(',')) <= allowed for r in res['runs'].values() for _, a in r['axioms'])
src_all = ''.join((R / 'src' / f'{m}.lean').read_text() for m in order)
res['forbidden_tokens'] = sorted(set(re.findall(r'\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^\s*axiom\b', src_all, flags=re.M)) - {''})
res['all_ok'] = ok and not bad and not missing and res['axioms_ok']
(R / 'ROOT-REPLAY.json').write_text(json.dumps(res, indent=1))
print(json.dumps({k: v for k, v in res.items() if k != 'runs'}, indent=1))
print('failed modules:', {m: (r['compile'], r['kernel']) for m, r in res['runs'].items() if r['compile'] != 0 or r['kernel'] != 0})
print('modules ok:', len(done), 'of', len(order))
