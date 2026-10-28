#!/usr/bin/env python3
"""Fresh strict replay of integrated Gamma support; no full source endpoint."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, tempfile

base = Path(__file__).resolve().parent
formal = base / 'formal'
modules = ['GammaDefs', 'ProfileConvex', 'StrictJensen', 'ConvexAssembly', 'GammaEuler', 'GammaRatio', 'GammaAssembly']
pins = json.loads((base / 'pins.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(Path(pins['lean_binary'])) == pins['lean_sha256']
assert subprocess.check_output([pins['lean_binary'], '--version'], text=True).strip() == pins['lean_version']
for name, entry in pins['packages'].items():
    assert subprocess.check_output(['git', '-C', entry['path'], 'rev-parse', 'HEAD'], text=True).strip() == entry['revision'], name
assert pins['packages']['mathlib']['revision'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
names = []
for module in modules:
    source = (formal / (module + '.lean')).read_text()
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', source), module
    names.extend(re.findall(r"^(?:noncomputable )?(?:def|theorem|lemma) ([\w']+)", source, re.M))
assert len(names) == 28 and len(set(names)) == 28
out = base / 'verification'
out.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='gamma-integration-fresh-') as temp:
    target = Path(temp)
    for filename in [*(m + '.lean' for m in modules), 'Checks.lean', 'run_lean.py']:
        shutil.copy2(formal / filename, target / filename)
    for module in modules:
        result = subprocess.run(['python3', 'run_lean.py', '-DwarningAsError=true', '-o', module + '.olean', module + '.lean'], cwd=target, capture_output=True, text=True)
        (out / (module + '.log')).write_text(result.stdout + result.stderr)
        assert result.returncode == 0 and not result.stdout and not result.stderr, (module, result.returncode, result.stdout, result.stderr)
    result = subprocess.run(['python3', 'run_lean.py', '-DwarningAsError=true', 'Checks.lean'], cwd=target, capture_output=True, text=True)
    (out / 'Checks.log').write_text(result.stdout + result.stderr)
    assert result.returncode == 0 and not result.stderr
    reports = re.findall(r"^'(.+)' depends on axioms: \[([^]]*)\]", result.stdout, re.M)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert {n for n, _ in reports} == {'GammaLevel.' + n for n in names}
    for name, axioms in reports:
        assert set(filter(None, axioms.split(', '))) <= allowed, (name, axioms)
    audit = {'status': 'PASS integrated Gamma component; full source endpoint absent', 'modules': len(modules), 'declarations': len(names), 'warnings_as_errors': True, 'fresh_source_copy': True, 'allowed_axioms': sorted(allowed), 'source_hashes': {m + '.lean': sha(target / (m + '.lean')) for m in modules}, 'scope': 'genuine Gamma strict mixture closed; strictAnti and level existence remain explicit assembly premises', 'pins_sha256': sha(base / 'pins.json')}
    (out / 'audit.json').write_text(json.dumps(audit, indent=2) + '\n')
print('PASS: fresh integrated Gamma component, 7 modules, 28 declarations, standard three axioms')
