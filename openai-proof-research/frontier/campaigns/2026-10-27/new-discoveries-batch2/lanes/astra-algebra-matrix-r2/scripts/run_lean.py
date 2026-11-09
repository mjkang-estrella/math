"""Compile and audit the partial bridge only; not the source conjecture."""
from pathlib import Path
import os, subprocess, json, hashlib, re
B = Path(__file__).resolve().parents[1]
packages = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
required_rev = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
manifest = json.loads((packages.parents[1]/'lake-manifest.json').read_text())
assert next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib') == required_rev
assert (packages/'mathlib/.git/HEAD').read_text().strip() == required_rev
lean = '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
build = B / 'verification' / 'fresh'
build.mkdir(exist_ok=True)
env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(build)] + [str(p/'.lake/build/lib/lean') for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir()]))
modules = ['ParameterObstruction']
names = []
hashes = {}
for mod in modules:
    src = B/'formal'/f'{mod}.lean'
    txt = src.read_text()
    if re.search(r'\b(sorry|admit|unsafe|native_decide)\b|^\s*axiom\b', txt, re.M):
        raise RuntimeError('forbidden token')
    names += ['MultiplicativeBasisObstruction.'+n for n in re.findall(r'^\s*(?:theorem|def)\s+(\w+)', txt, re.M)]
    hashes[src.name] = hashlib.sha256(src.read_bytes()).hexdigest()
    (build/src.name).write_bytes(src.read_bytes())
(build/'Checks.lean').write_text('\n'.join('import '+m for m in modules)+'\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n')
for mod in modules + ['Checks']:
    proc = subprocess.run([lean, '-DwarningAsError=true', '-o', str(build/f'{mod}.olean'), str(build/f'{mod}.lean')], cwd=build, env=env, capture_output=True, text=True)
    log = proc.stdout + proc.stderr
    (build/f'{mod}.log').write_text(log)
    print(mod, proc.returncode, flush=True)
    if proc.returncode:
        print(log)
        raise SystemExit(proc.returncode)
reports = re.findall(r"'([\w.]+)' depends on axioms: \[(.*?)\]", log, re.S)
pure = re.findall(r"'([\w.]+)' does not depend on any axioms", log)
assert sorted([n for n,a in reports]+pure) == sorted(names)
axioms = sorted({a.strip() for n,aa in reports for a in aa.split(',') if a.strip()})
assert set(axioms) <= {'propext','Classical.choice','Quot.sound'}
out = dict(status='PASS_PARTIAL_BRIDGE', literal_source_conjecture=False, declarations=names, axioms=axioms, hashes=hashes, compiler=subprocess.check_output([lean,'--version'],text=True).strip(), mathlib_required=required_rev, mathlib_head_and_manifest_verified=True)
(B/'verification'/'result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
