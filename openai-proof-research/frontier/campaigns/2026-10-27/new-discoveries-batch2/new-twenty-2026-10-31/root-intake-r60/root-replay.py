#!/usr/bin/env python3
"""Root replay: extract Lean modules from LEAN-SOURCE-APPENDIX.md of an author packet into a fresh dir, rebuild, kernel-check.
Usage: root-replay.py AUTHOR_PACKET_DIR REPLAY_DIR CPUS(e.g. 6,7)"""
import re, sys, hashlib, shutil, subprocess, json, os
from pathlib import Path
A = Path(sys.argv[1]).resolve(); R = Path(sys.argv[2]).resolve(); cpus = sys.argv[3]
assert not R.exists(), 'replay dir exists'
(R / 'src').mkdir(parents=True); (R / 'build').mkdir(); (R / 'cache').mkdir()
for f in ('run_lean_32g.py', 'formal_command.py', 'check32.sh', 'checker32.sh', 'write_lane.py', 'PINS.json'):
    shutil.copy2(A / f, R / f)
for f in ('check32.sh', 'checker32.sh'): os.chmod(R / f, 0o755)
t = (A / 'LEAN-SOURCE-APPENDIX.md').read_text()
blocks = re.findall(r'^#+[^\n`A-Za-z]*`?([A-Za-z][A-Za-z0-9_]*)(?:\.lean)?`?[^\n]*\n+```lean\n(.*?)\n```[ \t]*$', t, flags=re.S | re.M)
order, bad = [], []
for name, body in blocks:
    body += '\n'; (R / 'src' / f'{name}.lean').write_text(body); order.append(name)
    src = A / 'src' / f'{name}.lean'
    if not src.exists() or hashlib.sha256(body.encode()).hexdigest() != hashlib.sha256(src.read_bytes()).hexdigest(): bad.append(name)
missing = sorted(set(p.stem for p in (A / 'src').glob('*.lean')) - set(order))
res = {'modules': order, 'appendix_vs_author_src_mismatch': bad, 'author_src_not_in_appendix': missing, 'runs': {}}
ok = True
for m in order:
    c = subprocess.run(['taskset', '-c', cpus, './check32.sh', m, f'root-compile-{m}'], cwd=R, capture_output=True, text=True)
    (R / f'root-compile-{m}.console.txt').write_text(c.stdout + c.stderr)
    k = subprocess.run(['taskset', '-c', cpus, './checker32.sh', m, f'root-kernel-{m}'], cwd=R, capture_output=True, text=True)
    (R / f'root-kernel-{m}.console.txt').write_text(k.stdout + k.stderr)
    same = None
    ao, ro = A / 'build' / f'{m}.olean', R / 'build' / f'{m}.olean'
    if ao.exists() and ro.exists(): same = hashlib.sha256(ao.read_bytes()).hexdigest() == hashlib.sha256(ro.read_bytes()).hexdigest()
    res['runs'][m] = {'compile': c.returncode, 'kernel': k.returncode, 'olean_matches_author': same}
    ok &= c.returncode == 0 and k.returncode == 0
    ax = sorted(set(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", c.stdout)))
    res['runs'][m]['axioms'] = ax
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
res['axioms_ok'] = all(set(x.strip() for x in a.split(',')) <= allowed for r in res['runs'].values() for _, a in r['axioms'])
src_all = ''.join((R / 'src' / f'{m}.lean').read_text() for m in order)
res['forbidden_tokens'] = sorted(set(re.findall(r'\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^\s*axiom\b', src_all, flags=re.M)) - {''})
res['all_ok'] = ok and not bad and not missing and res['axioms_ok']
(R / 'ROOT-REPLAY.json').write_text(json.dumps(res, indent=1))
print(json.dumps({k: v for k, v in res.items() if k != 'runs'}, indent=1))
print('per-module:', {m: (r['compile'], r['kernel'], r['olean_matches_author']) for m, r in res['runs'].items()})
