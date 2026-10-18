#!/usr/bin/env python3
"""Independent reviewer build for T027O scoped support (MIT). Writes only to --output."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
CAMPAIGN = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14')
INPUT = CAMPAIGN / 't027o-formal-v1'
CACHE = CAMPAIGN / 'formal/.lake/packages'
INPUT_ANCHOR = 'b35948fddec735c7d9f0ed742d8158f4787f571cd69175a01f4db7ce2add46a4'
PINS = {'T027O.lean': '175680a36996718ad7fdf6aeb6fa5823c07d250e1b8bb43845a84c43e8a4e920',
        'Controls.lean': '58b19c1037e343b0879f798daca4a6d4f62202f297456d27577e9d05f78adaf1'}
REVIEW_SOURCE = 'T027OReview.lean'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = r'\b(?:sorry|admit|unsafe|native_decide|implemented_by|extern|opaque|axiom|macro|elab|syntax|notation|infix|infixl|infixr|prefix|postfix|set_option|run_cmd|initialize|instance|local)\b'

def need(ok, message):
    if not ok:
        raise SystemExit('INDEPENDENT_BUILD_FAIL: ' + message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def declarations(code, namespace):
    names, stack = [], []
    for line in code.splitlines():
        m = re.match(r'^namespace (\S+)', line)
        if m:
            stack.append(m.group(1))
        elif re.match(r'^end\s', line) and stack:
            stack.pop()
        m = re.match(r'^(?:noncomputable )?(def|theorem|lemma|abbrev|example|instance|structure|inductive|class) (\S+)', line)
        if m:
            need(m.group(1) in ('def', 'theorem'), 'unexpected declaration kind: ' + line)
            names.append('.'.join(stack + [m.group(2)]))
    need(all(n.startswith(namespace + '.') for n in names), 'namespace drift')
    return names

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', required=True)
    ap.add_argument('--lean', type=Path, default=LEAN)
    ap.add_argument('--cache', type=Path, default=CACHE)
    a = ap.parse_args()
    out = Path(a.output).resolve()
    need(not out.is_relative_to(INPUT) and not out.is_relative_to(HERE), 'output inside protected tree')
    out.mkdir(parents=True, exist_ok=False)
    raw = (INPUT / 'manifest.json').read_bytes()
    need(sha(raw) == INPUT_ANCHOR, 'input external anchor')
    manifest = json.loads(raw)
    for name, pin in PINS.items():
        data = (INPUT / name).read_bytes()
        need(sha(data) == pin and manifest['files'][name]['sha256'] == pin, 'input pin ' + name)
    lock = json.loads((INPUT / 'lake-manifest.json').read_text())
    env = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
    pins, libs = {}, []
    for entry in lock['packages']:
        dep = a.cache / entry['name']
        head = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], text=True, env=env).strip()
        dirty = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain', '--untracked-files=no'], text=True, env=env)
        need(head == entry['rev'] and not dirty.strip(), 'dependency ' + entry['name'])
        pins[entry['name']] = head
        lib = dep / '.lake/build/lib/lean'
        if lib.is_dir():
            libs.append(str(lib.resolve()))
    need(pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'mathlib pin')
    version = subprocess.check_output([str(a.lean), '--version'], text=True).strip()
    need('4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version, 'compiler')
    build = out / 'build'
    build.mkdir()
    sources = {'T027O.lean': ('T027O', INPUT / 'T027O.lean'),
               'Controls.lean': ('T027OControls', INPUT / 'Controls.lean'),
               REVIEW_SOURCE: ('T027OReview', HERE / REVIEW_SOURCE)}
    decls, source_hashes = {}, {}
    for name, (namespace, path) in sources.items():
        data = path.read_bytes()
        code = data.decode()
        need(not re.search(FORBIDDEN, re.sub(r'/-.*?-/', '', code, flags=re.S)), 'forbidden token in ' + name)
        (build / name).write_bytes(data)
        decls[name] = declarations(code, namespace)
        source_hashes[name] = sha(data)
    checks = ''.join('import ' + Path(n).stem + '\n' for n in sources) + '\n'
    checks += ''.join('#check @%s\n#print axioms %s\n' % (d, d) for ds in decls.values() for d in ds)
    (build / 'ReviewChecks.lean').write_text(checks)
    lean_env = dict(env, LEAN_PATH=os.pathsep.join([str(build)] + libs))
    runs = []
    steps = [('support', ['-o', 'T027O.olean', 'T027O.lean']),
             ('controls', ['-o', 'Controls.olean', 'Controls.lean']),
             ('review', ['-o', 'T027OReview.olean', REVIEW_SOURCE]),
             ('types-axioms', ['ReviewChecks.lean'])]
    for label, argv in steps:
        r = subprocess.run([str(a.lean), *argv], cwd=build, env=lean_env, capture_output=True, text=True)
        text = r.stdout + r.stderr
        (out / (label + '.log')).write_text(text)
        runs.append({'step': label, 'exit_code': r.returncode, 'output_sha256': sha(text.encode())})
        need(r.returncode == 0 and not re.search(r'\b(?:error|warning):', text), label + ' failed or warned:\n' + text)
    text = (out / 'types-axioms.log').read_text()
    axioms = {}
    for ds in decls.values():
        for d in ds:
            m = re.search("'" + re.escape(d) + r"' depends on axioms: \[([^\]]*)\]", text)
            got = set(x.strip() for x in m.group(1).split(',')) if m else set()
            need(m or ("'%s' does not depend on any axioms" % d) in text, 'missing axiom report ' + d)
            need(got <= STANDARD, 'nonstandard axiom in ' + d + ': ' + str(got))
            axioms[d] = sorted(got)
    olean = sorted(p.name for p in build.iterdir() if p.suffix in ('.olean', '.ilean'))
    for p in list(build.iterdir()):
        if p.suffix in ('.olean', '.ilean'):
            p.unlink()
    receipt = {'status': 'PASS_INDEPENDENT_BUILD_TYPES_STANDARD_AXIOMS', 'lean_version': version,
               'lean_binary_sha256': sha(a.lean.read_bytes()), 'dependencies': pins,
               'input_manifest_sha256': INPUT_ANCHOR, 'sources': source_hashes,
               'declarations': decls, 'kernel_dependencies': axioms, 'runs': runs,
               'objects_compiled_then_removed': olean, 'checks_lean_sha256': sha(checks.encode()),
               'full_theorem_formalized': False}
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(receipt['status'], {k: len(v) for k, v in decls.items()})

if __name__ == '__main__':
    main()
