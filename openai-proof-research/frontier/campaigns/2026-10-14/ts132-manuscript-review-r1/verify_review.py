#!/usr/bin/env python3
"""Read-only detached review verifier. Original code by Myeongjin Kang, MIT.
The identical verifier is shared by the two TS132 review packets; no private
source body or executable dependency object is redistributed.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe(name):
    p = PurePosixPath(name)
    require(isinstance(name, str) and name and not p.is_absolute()
            and '..' not in p.parts and str(p) == name, 'unsafe relative path')
    return name


def inventory(root, manifest_name, anchor, ignore=None):
    require(not root.is_symlink(), 'symlink root')
    mf = root / manifest_name
    require(not mf.is_symlink() and digest(mf) == anchor, 'external manifest anchor mismatch')
    m = json.loads(mf.read_text())
    entries = m['files']
    names = [safe(e['path']) for e in entries]
    require(len(names) == len(set(names)), 'duplicate file entry')
    dirs = [safe(x) for x in m['directories']]
    require(len(dirs) == len(set(dirs)), 'duplicate directory entry')
    actual_files, actual_dirs = set(), set()
    for p in root.rglob('*'):
        rel = p.relative_to(root).as_posix()
        # Only the formal author's declared replay area is outside its seal.
        if ignore and (rel == ignore or rel.startswith(ignore + '/')):
            continue
        require(not p.is_symlink(), 'symlink: ' + rel)
        if p.is_dir():
            actual_dirs.add(rel)
        elif p.is_file():
            actual_files.add(rel)
        else:
            raise ValueError('unsupported filesystem entry: ' + rel)
    require(actual_files == set(names) | {manifest_name}, 'file membership mismatch')
    require(actual_dirs == set(dirs), 'directory membership mismatch')
    for e in entries:
        p = root / e['path']
        require(p.stat().st_size == e['bytes'] and digest(p) == e['sha256'],
                'payload mismatch: ' + e['path'])
    return m


def evidence(root, m):
    v = json.loads((root / 'verdict.json').read_text())
    require(v['verdict'] == m['verdict'], 'verdict disagreement')
    require(v['full_TS132_formalized'] is False and v['required_repairs'] == []
            and v['acceptance_or_publication'] is False, 'scope disagreement')
    require(v['reviewer_authored_prior_human_proof_review'] is True
            and v['reviewer_authored_reviewed_artifact'] is False, 'relationship disagreement')
    if v['gate'] == 'formal':
        require(v['verdict'] == 'PASS_SCOPED_SUPPORT', 'wrong formal verdict')
        r = json.loads((root / 'work/logs/fresh-build/receipt.json').read_text())
        require(r['full_TS132_theorem_formalized'] is False
                and r['previous_support_objects_used'] is False, 'build scope disagreement')
        require(len(r['support_theorems']) == 22 and len(r['control_theorems']) == 13
                and len(r['support_declarations']) + len(r['control_declarations']) == 43,
                'declaration count mismatch')
        for name, sha in r['source_sha256'].items():
            require(digest(root / 'work' / safe(name)) == sha, 'build source identity')
        for category in ['axiom_reports', 'control_axiom_reports']:
            require(all(set(xs) <= {'propext', 'Classical.choice', 'Quot.sound'}
                        for xs in r[category].values()), 'unexpected axioms')
        for run in r['runs']:
            require(run['exit_code'] == 0, 'failed build run')
            for stream in ['stdout', 'stderr']:
                p = root / 'work/logs/fresh-build' / (run['name'] + '.' + stream)
                require(digest(p) == run[stream + '_sha256'], 'build log identity')
        mutants = json.loads((root / 'work/logs/mutations/receipt.json').read_text())
        require(len(mutants['cases']) == 6 and mutants['source_sha256'] == r['source_sha256']['TSLocal.lean'], 'mutant identity')
        for c in mutants['cases']:
            require(c['exit_code'] != 0 and c['result'] == 'EXPECTED_PROOF_REJECTION', 'mutant unexpectedly accepted')
            require(digest(root / 'work/logs/mutations' / (safe(c['case']) + '.stdout')) == c['stdout_sha256'], 'mutant log identity')
        runner = json.loads((root / 'work/logs/runner-control/receipt.json').read_text())
        require(runner['actual_subprocess_control'] is True and runner['child_exit'] == 0
                and runner['wrapper_exit'] == 1 and runner['child_stdout'] == 'SOME FAIL\n', 'runner control mismatch')
    elif v['gate'] == 'manuscript':
        require(v['verdict'] == 'PASS_MANUSCRIPT', 'wrong manuscript verdict')
        r = json.loads((root / 'work/checks/build-receipt.json').read_text())
        qa = json.loads((root / 'visual-qa.json').read_text())
        expected = '580d2b10d7d74860a12c4f8ce4e066205b03b70b8b53e3a24b79ea8938efbdb5'
        require(r['pdf_sha256'] == qa['pdf_sha256'] == expected
                and digest(root / 'work/output/pdf/transitive-superquadratic-sensitivity.pdf') == expected, 'PDF identity')
        require(r['pdf_pages'] == r['rendered_pages'] == len(qa['pages']) == 9
                and qa['all_pages_independently_viewed'] is True and qa['required_repairs'] == [], 'visual evidence scope')
        require([p['page'] for p in qa['pages']] == list(range(1, 10)), 'page coverage')
        for p in qa['pages']:
            require(p['visually_inspected'] is True and digest(root / safe(p['file'])) == p['sha256'], 'raster identity')
        require(digest(root / 'work/main.tex') == r['source_sha256']
                and digest(root / 'work/formal-support.tex') == r['formal_support_sha256'], 'TeX identity')
    else:
        raise ValueError('unknown gate')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--dependency-parent', type=Path)
    args = ap.parse_args()
    root = Path(__file__).absolute().parent
    m = inventory(root, 'manifest.json', args.anchor)
    evidence(root, m)
    checked = 0
    if args.dependency_parent:
        a = json.loads((root / 'authentication.json').read_text())
        for item in a['packages']:
            rel = Path(safe(item['manifest']))
            ignore = '.replays' if rel.parent.name == 'ts132-formal-v1' else None
            dm = inventory(args.dependency_parent / rel.parent, rel.name, item['anchor'], ignore)
            require(len(dm['files']) == item['files'], 'dependency count')
            checked += 1
    print(json.dumps({'status': 'PASS', 'verdict': m['verdict'], 'payloads': len(m['files']),
                      'directories': len(m['directories']), 'live_dependency_packets': checked,
                      'full_TS132_formalized': False}))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as e:
        raise SystemExit('REJECT: ' + str(e))
