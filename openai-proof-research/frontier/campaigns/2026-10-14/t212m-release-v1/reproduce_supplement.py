#!/usr/bin/env python3
"""Clean replay of the separately reviewed T212M supplement. MIT.

Reads only explicitly anchored selected inputs; writes only a new output tree.
This is a reproducibility driver, not a new mathematical review or release gate.
Compiler and dependency build caches remain trusted, not rebuilt.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess

FORMAL = 'cc09818fed56aa44deda1f8fb9baf6d018bf6d4c3f8317f7bb6612f31624ce00'
REVIEW = '9e5a5cf03fab9b0759048f28848156d26d811981203df5e21b5ee556b5ea01fc'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def ancestry(path):
    require(path.is_absolute() and '..' not in path.parts, 'absolute normalized path required')
    for p in (*reversed(path.parents), path):
        require(not p.is_symlink(), 'symlink ancestry')


def read(root, name):
    parts = PurePosixPath(name).parts
    require(parts and not name.startswith('/') and '..' not in parts, 'unsafe relative name')
    p = root.joinpath(*parts)
    ancestry(p)
    st = p.stat()
    require(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'unsafe input file')
    return p.read_bytes()


def manifest(root, name, anchor):
    data = read(root, name)
    require(sha(data) == anchor, 'external manifest mismatch')
    return json.loads(data)['files']


def member(root, records, name):
    data = read(root, name)
    rec = records[name]
    require(sha(data) == rec['sha256'] and len(data) == rec['bytes'], 'anchored member mismatch: ' + name)
    return data


def fingerprint(root):
    rows = []
    for base, dirs, files in os.walk(root):
        dirs.sort()
        for name in sorted(files + dirs):
            p = Path(base) / name
            st = p.lstat()
            rows.append((p.relative_to(root).as_posix(), st.st_mode, st.st_size, st.st_mtime_ns, st.st_ctime_ns))
    return sha(json.dumps(rows, separators=(',', ':')).encode())


def main():
    ap = argparse.ArgumentParser()
    for name in ['formal', 'review', 'cache', 'lean', 'output']:
        ap.add_argument('--' + name, type=Path, required=True)
    ap.add_argument('--formal-anchor', required=True)
    ap.add_argument('--review-anchor', required=True)
    a = ap.parse_args()
    require(a.formal_anchor == FORMAL and a.review_anchor == REVIEW, 'wrong external anchors')
    for p in [a.formal, a.review, a.cache, a.lean, a.output]:
        ancestry(p)
    for source in [a.formal, a.review, a.cache, a.lean.parent]:
        require(not a.output.is_relative_to(source) and not source.is_relative_to(a.output), 'output overlaps inputs')
    require(not a.output.exists(), 'output must be new')
    fm = manifest(a.formal, 'manifest.json', FORMAL)
    rm = manifest(a.review, 'review-manifest.json', REVIEW)
    sources = {name: member(a.formal, fm, name) for name in ['T212M.lean', 'Controls.lean']}
    sources['Independent.lean'] = member(a.review, rm, 'Independent.lean')
    lock = json.loads(member(a.formal, fm, 'lake-manifest.json'))
    execution = json.loads(member(a.review, rm, 'execution.json'))
    expected_log = member(a.review, rm, 'independent-logs/Independent.lean.log')
    require(sha(expected_log) == execution['independent']['log_sha256'], 'review log binding mismatch')
    env = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
    pins, libs = {}, []
    for entry in lock['packages']:
        require(re.fullmatch(r'[A-Za-z0-9_-]+', entry['name']), 'unsafe dependency name')
        dep = a.cache / entry['name']
        ancestry(dep)
        head = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], env=env, text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain', '--untracked-files=no'], env=env, text=True)
        require(head == entry['rev'] and not dirty.strip(), 'dependency pin/cleanliness mismatch')
        extra = subprocess.check_output(['git', '-C', str(dep), 'ls-files', '--others', '--exclude-standard', '-z'], env=env)
        require(not any(n.endswith(b'.lean') for n in extra.split(b'\0')), 'untracked dependency Lean source')
        pins[entry['name']] = head
        lib = dep / '.lake/build/lib/lean'
        if lib.is_dir():
            libs.append(str(lib))
    require(pins == execution['pins_before']['dependencies'], 'review dependency set mismatch')
    version = subprocess.check_output([str(a.lean), '--version'], text=True).strip()
    require(version == execution['pins_before']['lean_version'], 'compiler version mismatch')
    require(sha(a.lean.read_bytes()) == execution['pins_before']['lean_sha256'], 'compiler binary mismatch')
    before = fingerprint(a.cache)
    a.output.mkdir(parents=True, exist_ok=False)
    build = a.output / 'build'
    build.mkdir()
    for name, data in sources.items():
        (build / name).write_bytes(data)
    env['LEAN_PATH'] = os.pathsep.join([str(build)] + sorted(libs))
    runs = []
    for name in sources:
        argv = [str(a.lean)]
        if name != 'Independent.lean':
            argv += ['-o', Path(name).stem + '.olean']
        result = subprocess.run(argv + [name], cwd=build, env=env, capture_output=True)
        log = result.stdout + result.stderr
        (a.output / (name + '.log')).write_bytes(log)
        require(result.returncode == 0 and not re.search(rb'\b(?:error|warning):', log), 'compilation failed: ' + name)
        runs.append({'file': name, 'exit_code': result.returncode, 'log_sha256': sha(log)})
    require(log == expected_log, 'review inventory log differs')
    require(before == fingerprint(a.cache), 'dependency cache changed')
    for name, data in sources.items():
        root, records = (a.review, rm) if name == 'Independent.lean' else (a.formal, fm)
        require(member(root, records, name) == data, 'input changed during replay')
    receipt = {'status': 'PASS_REVIEWER_SUPPLEMENT_REPLAY', 'formal_anchor': FORMAL, 'review_anchor': REVIEW,
               'runs': runs, 'sources': {n: sha(d) for n, d in sources.items()}, 'dependencies': pins,
               'inventory_log_byte_identical': True, 'cache_metadata_unchanged': True,
               'full_theorem_formalized': False, 'new_independent_review': False,
               'trust': 'Exact compiler binary and cached dependency artifacts are trusted, not rebuilt.'}
    (a.output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
