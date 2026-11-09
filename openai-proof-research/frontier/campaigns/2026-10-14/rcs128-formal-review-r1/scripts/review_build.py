#!/usr/bin/env python3
"""Reviewer build of frozen RCS128 sources plus reviewer controls; MIT, Myeongjin Kang (review packet).

Copies RCS128.lean and Controls.lean from the frozen package after checking their
SHA256 against the frozen manifest (itself checked against the external anchor),
compiles them and checks/ReviewerControls.lean from source into a NEW output
directory, prints types and axioms of every reviewer declaration, rejects Lean
errors/warnings and nonstandard axioms, and replays the fresh modules through
the toolchain's leanchecker. Dependency .olean files are trusted read-only.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ANCHOR = 'c3a051864862ebf53c24fce85da991f2e1da18340d38afdae238f3a160361963'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = re.compile(r'\b(?:sorry|admit|unsafe|native_decide|implemented_by|extern|opaque|'
                       r'skipKernelTC|debug\.)\b|^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?axiom\s',
                       re.M)


def require(ok, message):
    if not ok:
        raise SystemExit('FAIL: ' + message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(argv, cwd, env, log):
    result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True)
    text = result.stdout + result.stderr
    Path(log).write_text(text)
    return result.returncode, text


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--frozen', type=Path, required=True)
    parser.add_argument('--controls', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    args = parser.parse_args()
    frozen = args.frozen.resolve()
    raw = (frozen / 'manifest.json').read_bytes()
    require(sha(raw) == ANCHOR, 'frozen manifest anchor mismatch')
    manifest = json.loads(raw)
    out = args.output.resolve()
    require(not out.is_relative_to(frozen), 'output inside frozen package')
    out.mkdir(parents=True, exist_ok=False)
    build = out / 'build'
    build.mkdir()
    for name in ['RCS128.lean', 'Controls.lean']:
        data = (frozen / name).read_bytes()
        require(sha(data) == manifest['files'][name]['sha256'], 'frozen source hash: ' + name)
        (build / name).write_bytes(data)
    controls = args.controls.read_bytes()
    (build / 'ReviewerControls.lean').write_bytes(controls)
    for name in ['RCS128.lean', 'Controls.lean', 'ReviewerControls.lean']:
        require(not FORBIDDEN.search((build / name).read_text()), 'forbidden token: ' + name)
    lock = json.loads((frozen / 'lake-manifest.json').read_text())
    libs, pins = [], {}
    for entry in lock['packages']:
        dep = args.cache / entry['name']
        head = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], text=True).strip()
        require(head == entry['rev'], 'pin ' + entry['name'])
        dirty = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain'], text=True)
        require(not dirty.strip(), 'dependency worktree not clean (incl. untracked): ' + entry['name'])
        pins[entry['name']] = head
        lib = dep / '.lake/build/lib/lean'
        if lib.is_dir():
            libs.append(str(lib.resolve()))
    version = subprocess.check_output([str(args.lean), '--version'], text=True).strip()
    require('4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version, 'lean version')
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(build)] + libs)
    receipt = {'anchor': ANCHOR, 'lean_version': version, 'dependencies': pins,
               'reviewer_controls_sha256': sha(controls), 'steps': []}
    names = re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)', controls.decode(), re.M)
    checks = 'import ReviewerControls\n' + ''.join(
        f'#check @RCS128Review.{n}\n#print axioms RCS128Review.{n}\n' for n in names)
    (build / 'ReviewChecks.lean').write_text(checks)
    steps = [('support', [str(args.lean), '-o', 'RCS128.olean', 'RCS128.lean']),
             ('controls', [str(args.lean), '-o', 'Controls.olean', 'Controls.lean']),
             ('reviewer-controls', [str(args.lean), '-o', 'ReviewerControls.olean', 'ReviewerControls.lean']),
             ('reviewer-types-axioms', [str(args.lean), 'ReviewChecks.lean'])]
    for label, argv in steps:
        code, text = run(argv, build, env, out / (label + '.log'))
        receipt['steps'].append({'step': label, 'exit_code': code, 'output_sha256': sha(text.encode())})
        require(code == 0 and not re.search(r'\b(?:error|warning):', text), 'compile failed or warned: ' + label)
    text = (out / 'reviewer-types-axioms.log').read_text()
    axioms = {}
    for n in names:
        full = 'RCS128Review.' + n
        m = re.search("'" + re.escape(full) + r"' depends on axioms: \[([^\]]*)\]", text)
        if m:
            found = set(a.strip() for a in m.group(1).split(',')) - {''}
        else:
            require("'" + full + "' does not depend on any axioms" in text, 'missing axiom report ' + full)
            found = set()
        require(found <= STANDARD, 'nonstandard axiom in ' + full)
        axioms[full] = sorted(found)
    receipt['reviewer_declarations'] = len(names)
    receipt['reviewer_axioms'] = axioms
    checker = args.lean.parent / 'leanchecker'
    for module in ['RCS128', 'Controls', 'ReviewerControls']:
        code, text = run([str(checker), module], build, env, out / ('leanchecker-' + module + '.log'))
        receipt['steps'].append({'step': 'leanchecker ' + module, 'exit_code': code,
                                 'output_sha256': sha(text.encode())})
        require(code == 0 and not re.search(r'\b(?:error|warning)\b', text, re.I), 'leanchecker ' + module)
    for p in build.glob('*.olean'):
        p.unlink()
    receipt['status'] = 'PASS_REVIEWER_BUILD_CONTROLS_AND_KERNEL_REPLAY'
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(receipt['status'], len(names), 'reviewer declarations')


if __name__ == '__main__':
    main()
