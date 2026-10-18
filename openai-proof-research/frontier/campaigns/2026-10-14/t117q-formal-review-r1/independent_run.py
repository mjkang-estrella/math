#!/usr/bin/env python3
"""Reviewer-side independent compile of the frozen T117Q sources plus reviewer controls.

MIT, t117q-formal-review-r1. Authenticates the frozen packet by its external anchor first,
then copies sources into a NEW directory under /var/tmp. Never writes into the frozen packet
or the dependency cache. Logs go to --logs (a new directory).
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent / 't117q-formal-v1'
CACHE = HERE.parent / 'formal/.lake/packages'
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
ANCHOR = 'b741e2d76e9383238b5f3e975c634e2bb48b75eaa00dc1fb93371b0a1c139b37'
SOURCES = {'T117Q.lean': 'bdb2a4d205043cc71517e49123a32855a712f066fe860b53c0cee9f40d8cfa9f',
           'Controls.lean': 'c5a574b41a5f9341216ed95635eacd5bcd585baf99b1c01756b1a212baedf2fb'}
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise SystemExit('FAIL: ' + message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--logs', required=True, type=Path)
    args = parser.parse_args()
    logs = args.logs.resolve()
    require(not logs.is_relative_to(PACKET.resolve()), 'logs inside frozen packet')
    logs.mkdir(parents=True, exist_ok=False)
    check = subprocess.run(['python3', '-B', str(PACKET / 'verify.py'), '--anchor', ANCHOR],
                           capture_output=True, text=True)
    require(check.returncode == 0, 'packet anchor verification failed: ' + check.stderr)
    manifest = json.loads((PACKET / 'manifest.json').read_bytes())
    for name, digest in SOURCES.items():
        require(manifest['files'][name]['sha256'] == digest, 'manifest source hash ' + name)
        require(sha((PACKET / name).read_bytes()) == digest, 'source hash ' + name)
    lock = json.loads((PACKET / 'lake-manifest.json').read_text())
    libs, pins = [], {}
    for entry in lock['packages']:
        dep = CACHE / entry['name']
        rev = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], text=True).strip()
        require(rev == entry['rev'], 'pin ' + entry['name'])
        dirty = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain',
                                         '--untracked-files=no'], text=True)
        require(not dirty.strip(), 'dirty dependency ' + entry['name'])
        pins[entry['name']] = rev
        libs.append(str((dep / '.lake/build/lib/lean').resolve()))
    require(len(pins) == 9 and pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'pins')
    version = subprocess.check_output([str(LEAN), '--version'], text=True).strip()
    require('4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version, 'lean')
    receipt = {'packet_anchor': ANCHOR, 'lean_version': version,
               'lean_binary_sha256': sha(LEAN.read_bytes()), 'dependencies': pins,
               'independent_lean_sha256': sha((HERE / 'Independent.lean').read_bytes()),
               'runs': []}
    with tempfile.TemporaryDirectory(prefix='t117q-review-independent-', dir='/var/tmp') as tmp:
        build = Path(tmp)
        for name in SOURCES:
            (build / name).write_bytes((PACKET / name).read_bytes())
        (build / 'Independent.lean').write_bytes((HERE / 'Independent.lean').read_bytes())
        indep = (HERE / 'Independent.lean').read_text()
        require(not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s', indep, re.M),
                'escape in Independent.lean')
        own = ['T117QReview.' + n for n in
               re.findall(r'^(?:noncomputable )?(?:abbrev|def|theorem) (\w+)', indep, re.M)]
        (build / 'ReviewAxioms.lean').write_text(
            'import Independent\n' + ''.join('#check @%s\n#print axioms %s\n' % (n, n) for n in own))
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(build)] + libs))
        steps = [('support', ['-o', 'T117Q.olean', 'T117Q.lean']),
                 ('controls', ['-o', 'Controls.olean', 'Controls.lean']),
                 ('independent', ['-o', 'Independent.olean', 'Independent.lean']),
                 ('review-axioms', ['ReviewAxioms.lean'])]
        for label, argv in steps:
            result = subprocess.run([str(LEAN), *argv], cwd=build, env=env,
                                    capture_output=True, text=True)
            text = result.stdout + result.stderr
            (logs / (label + '.log')).write_text(text)
            receipt['runs'].append({'step': label, 'exit_code': result.returncode,
                                    'output_sha256': sha(text.encode())})
            require(result.returncode == 0 and not re.search(r'\b(?:error|warning):', text),
                    'step failed or warned: ' + label + '\n' + text)
        text = (logs / 'review-axioms.log').read_text()
        axioms = {}
        for n in own:
            m = re.search("'" + re.escape(n) + r"' depends on axioms: \[([^\]]*)\]", text)
            got = set(re.split(r',\s*', m.group(1).strip())) - {''} if m else set()
            require(m or ("'" + n + "' does not depend on any axioms") in text, 'axiom report ' + n)
            require(got <= STANDARD, 'nonstandard axiom in ' + n)
            axioms[n] = sorted(got)
        receipt['reviewer_declarations'] = axioms
        ind = (logs / 'independent.log').read_text()
        counts = re.findall(r'module (\w+): (\d+) constants total, (\d+) non-internal', ind)
        receipt['kernel_enumeration'] = {m: {'total': int(t), 'non_internal': int(p)}
                                         for m, t, p in counts}
    receipt['status'] = 'PASS_REVIEWER_INDEPENDENT_COMPILE'
    (logs / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(receipt['status'], json.dumps(receipt['kernel_enumeration']))


if __name__ == '__main__':
    main()
