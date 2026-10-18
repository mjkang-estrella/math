#!/usr/bin/env python3
"""T205M scoped formal review r1 execution; MIT, reviewer-written.

Writes only inside this review directory and new /var/tmp directories. The frozen
packet and the shared dependency cache are read only; the cache is fingerprinted
before and after. No mathematical verdict is produced by this script.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import tempfile

ANCHOR = '3037eddfa1f64be85b646090df0f49484b84ff625eb0970074af86c3948ce2f2'
REVIEW = Path(__file__).resolve().parent
CAMPAIGN = REVIEW.parent
PACKET = CAMPAIGN / 't205m-formal-v1'
CACHE = CAMPAIGN / 'formal/.lake/packages'
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
LEAN_COMMIT = '5045d0056413266e57c625dcd7c365b10e377c52'
MATHLIB = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
DISPATCH_INPUTS = {
    'inputs/author-manifest.json': '29ab2fdb5cf45be3a9a1d36742e5b730a756ee27459fb0d900764d3c14d41db9',
    'inputs/candidate205m.md': '17b2b35c42ef10fd0600e0a7b4b5897f0b80cd57cfb1e12587b722294a3e20c5',
    'inputs/parent-high-capacity.md': 'fc155c9ac03d70b8a68f501541daf0fb5c02bf9caf6734f61757065a6e796430',
}
AUDITED = [
    'T205M.IsIdeal', 'T205M.empty_ideal', 'T205M.ideal_insert_minimal',
    'T205M.ideal_interval_rank', 'T205M.unique_rank_cross_comparable',
    'T205M.exists_second_ideal_of_incomparable', 'T205M.two_ideals_of_no_cut',
    'T205MControls.chainPrefix', 'T205MControls.chainPrefix_ideal',
    'T205MControls.chainPrefix_unique', 'T205MControls.chainPrefix_cross',
    'T205MControls.product_has_rank_four', 'T205MControls.antichain_singleton_ideal',
    'T205MControls.antichain_noncomparable', 'T205MControls.antichain_second_ideal',
    'T205MControls.uniqueness_cannot_be_dropped',
    'T205MControls.rank_upper_bound_cannot_be_dropped',
]
INSTANCES = ['T205MControls.Two._sizeOf_inst', 'T205MControls.instDecidableEqTwo',
             'T205MControls.instDecidableLETwo', 'T205MControls.instFintypeTwo',
             'T205MControls.instPartialOrderTwo']
FORBIDDEN = re.compile(r'\b(?:sorry|admit|unsafe|native_decide|axiom|implemented_by|extern)\b')
REVIEWER_FORBIDDEN = re.compile(r'\b(?:sorry|admit|unsafe|native_decide|implemented_by|extern)\b'
                                r'|^\s*(?:private\s+|protected\s+)?axiom\s', re.M)
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def authenticate(root):
    raw = (root / 'manifest.json').read_bytes()
    require(sha(raw) == ANCHOR, 'packet anchor mismatch')
    manifest = json.loads(raw)
    files, dirs = {}, []
    for base, ds, fs in os.walk(root):
        for name in ds + fs:
            p = Path(base) / name
            st = p.lstat()
            rel = p.relative_to(root).as_posix()
            require(not stat.S_ISLNK(st.st_mode), 'symlink ' + rel)
            if stat.S_ISDIR(st.st_mode):
                dirs.append(rel)
                continue
            require(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'unsafe ' + rel)
            if rel != 'manifest.json':
                data = p.read_bytes()
                files[rel] = {'bytes': len(data), 'sha256': sha(data)}
    require(files == manifest['files'] and sorted(dirs) == manifest['directories'],
            'packet inventory mismatch')
    for rel, digest in DISPATCH_INPUTS.items():
        require(files[rel]['sha256'] == digest, 'dispatch input mismatch ' + rel)
    for rel, entry in json.loads((root / 'provenance.json').read_text())['inputs'].items():
        original = (CAMPAIGN.parent.parent.parent / entry['original_path']).read_bytes()
        require(sha(original) == entry['sha256'] == files['inputs/' + rel]['sha256'],
                'copied input differs from original ' + rel)
    return {'manifest_sha256': ANCHOR, 'files': len(files), 'directories': sorted(dirs)}


def cache_fingerprint():
    rows = []
    for base, ds, fs in os.walk(CACHE):
        ds.sort()
        for name in sorted(fs) + ds:
            p = Path(base) / name
            st = p.lstat()
            rows.append('%s\t%o\t%d\t%d\t%d' % (p.relative_to(CACHE).as_posix(), st.st_mode,
                                                st.st_size, st.st_mtime_ns, st.st_ctime_ns))
    return {'entries': len(rows), 'sha256': sha('\n'.join(rows).encode())}


def pins():
    lock = json.loads((PACKET / 'lake-manifest.json').read_text())
    found = {}
    for entry in lock['packages']:
        dep = CACHE / entry['name']
        head = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], text=True, env=ENV).strip()
        dirty = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain', '--untracked-files=no'],
                                        text=True, env=ENV)
        require(head == entry['rev'] and not dirty.strip(), 'pin or cleanliness failure ' + entry['name'])
        found[entry['name']] = head
    require(len(found) == 9 and found['mathlib'] == MATHLIB, 'expected nine pins with mathlib')
    version = subprocess.check_output([str(LEAN), '--version'], text=True).strip()
    require('4.34.1' in version and LEAN_COMMIT in version, 'wrong Lean')
    return {'dependencies': found, 'lean_version': version, 'lean_sha256': sha(LEAN.read_bytes())}


def lean_path(build):
    libs = sorted(str(p.resolve()) for p in CACHE.glob('*/.lake/build/lib/lean'))
    return os.pathsep.join([str(build)] + libs)


def compile_chain(build, files):
    env = dict(ENV, LEAN_PATH=lean_path(build))
    out = []
    for name, emit in files:
        argv = [str(LEAN)] + (['-o', Path(name).stem + '.olean'] if emit else []) + [name]
        r = subprocess.run(argv, cwd=build, env=env, capture_output=True, text=True)
        text = r.stdout + r.stderr
        out.append({'file': name, 'exit_code': r.returncode, 'output': text})
        if r.returncode or re.search(r'\b(?:error|warning):', text):
            break
    return out


def run_builder(packet_copy, output, defaults=False):
    extra = [] if defaults else ['--cache', str(CACHE), '--lean', str(LEAN)]
    r = subprocess.run(['python3', '-B', str(packet_copy / 'rebuild.py'), '--output', str(output)] + extra,
                       cwd='/var/tmp', env=ENV, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def main():
    work = Path(tempfile.mkdtemp(prefix='t205m-formal-review-r1-', dir='/var/tmp'))
    record = {'status': 'RUNNING', 'work_directory': str(work), 'anchor': ANCHOR}
    record['authentication_before'] = authenticate(PACKET)
    record['pins_before'] = pins()
    record['cache_before'] = cache_fingerprint()

    code, text = run_builder(PACKET, work / 'builder-output', defaults=True)
    require(code == 0 and 'PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS' in text
            and 'Support declarations: 7' in text and 'Control declarations: 10' in text, 'builder failed')
    copy = REVIEW / 'builder-run'
    if copy.exists():
        shutil.rmtree(copy)
    shutil.copytree(work / 'builder-output', copy)
    (copy / 'stdout.txt').write_text(text)
    fresh = json.loads((copy / 'receipt.json').read_text())
    frozen = json.loads((PACKET / 'validation/receipt.json').read_text())
    for key in ['status', 'sources', 'dependencies', 'lean_version', 'lean_binary_sha256',
                'kernel_dependencies', 'declarations', 'dependency_cache_modified']:
        require(fresh[key] == frozen[key], 'fresh receipt differs: ' + key)
    for name in ['Checks.lean', 'types-axioms.log', 'support.log', 'controls.log']:
        require((copy / name).read_bytes() == (PACKET / 'validation' / name).read_bytes(),
                'fresh log differs: ' + name)
    require(sorted(sum(fresh['declarations'].values(), [])) == sorted(AUDITED), 'audited set differs')
    for name, axioms in fresh['kernel_dependencies'].items():
        require(set(axioms) <= STANDARD, 'axiom ' + name)
    record['builder'] = {'exit_code': code, 'receipt_sha256': sha((copy / 'receipt.json').read_bytes()),
                         'logs_identical_to_frozen_validation': True, 'audited_declarations': len(AUDITED)}

    for name in ['T205M.lean', 'Controls.lean']:
        code_text = (PACKET / name).read_text()
        require(not FORBIDDEN.search(code_text), 'forbidden token ' + name)
    independent_source = (REVIEW / 'Independent.lean').read_text()
    require(not REVIEWER_FORBIDDEN.search(independent_source), 'forbidden token Independent.lean')
    build = work / 'independent'
    build.mkdir()
    for name in ['T205M.lean', 'Controls.lean']:
        shutil.copyfile(PACKET / name, build / name)
    shutil.copyfile(REVIEW / 'Independent.lean', build / 'Independent.lean')
    steps = compile_chain(build, [('T205M.lean', True), ('Controls.lean', True), ('Independent.lean', False)])
    logs = REVIEW / 'independent-logs'
    logs.mkdir(exist_ok=True)
    for step in steps:
        (logs / (step['file'] + '.log')).write_text(step['output'])
    require(len(steps) == 3 and all(s['exit_code'] == 0 for s in steps), 'independent compile failed')
    require(not any(re.search(r'\b(?:error|warning):', s['output']) for s in steps), 'independent warnings')
    inv = steps[2]['output']
    require('INDEPENDENT_INVENTORY_PASS' in inv and 'MODULE T205M constants=12' in inv
            and 'MODULE Controls constants=41' in inv, 'independent inventory failed')
    listed = re.findall(r'^  (\S+) kind=(\w+)((?: instance)?)((?: internal)?) axioms=\[([^\]]*)\]', inv, re.M)
    names = {n for n, *_ in listed}
    require(set(AUDITED) <= names, 'audited declaration missing from inventory')
    instances = sorted(n for n, _, i, *_ in listed if i)
    require(instances == INSTANCES, 'instance set differs: %s' % instances)
    record['independent'] = {
        'constants_T205M_module': 12, 'constants_Controls_module': 41,
        'instances': instances, 'all_axioms_standard': True,
        'reviewer_constants': int(re.search(r'REVIEWER constants=(\d+)', inv).group(1)),
        'log_sha256': sha(inv.encode())}

    r = subprocess.run(['python3', '-B', str(PACKET / 'integrity_controls.py'), '--anchor', ANCHOR],
                       cwd='/var/tmp', env=ENV, capture_output=True, text=True)
    require(r.returncode == 0, 'packet integrity controls failed: ' + r.stderr)
    integrity = json.loads(r.stdout)
    require(len(integrity['results']) == 15 and
            [x['accepted'] for x in integrity['results']] == [True] + [False] * 14, 'integrity outcome')
    (REVIEW / 'packet-integrity-controls.json').write_text(json.dumps(integrity, indent=2) + '\n')
    record['packet_integrity_controls'] = {'cases': 15, 'accepted_only': 'positive'}

    record['mutation_controls'] = mutation_controls(work)

    record['cache_after'] = cache_fingerprint()
    require(record['cache_after'] == record['cache_before'], 'dependency cache changed')
    record['pins_after'] = pins()
    record['authentication_after'] = authenticate(PACKET)
    status = subprocess.check_output(['git', '-C', str(PACKET), 'status', '--porcelain', '--', '.'],
                                     text=True, env=ENV)
    require(not status.strip(), 'frozen packet differs from git')
    record['packet_git_clean'] = True
    record['status'] = 'PASS_EXECUTION_ONLY'
    (REVIEW / 'execution.json').write_text(json.dumps(record, indent=2) + '\n')
    print(record['status'])


def mutate(path, old, new):
    text = path.read_text()
    require(text.count(old) == 1, 'mutation anchor not unique: ' + old)
    path.write_text(text.replace(old, new))


def mutation_controls(work):
    base = work / 'mutations'
    base.mkdir()
    ideal_def = '∀ ⦃x y : α⦄, y ∈ s → x ≤ y → x ∈ s'
    no_cut_sig = '    (hr : r ≤ Fintype.card α)\n'
    cases = [
        ('sorry-proof', 'builder', False, 'forbidden proof escape: T205M.lean',
         ('T205M.lean', 'exact hab (unique_rank_cross_comparable hs hu ha hb)', 'sorry')),
        ('declared-axiom', 'builder', False, 'forbidden proof escape: T205M.lean',
         ('T205M.lean', 'end T205M', 'axiom cheat : False\n\nend T205M')),
        ('private-axiom-dependency', 'builder', False, 'unapproved axiom dependency: T205M.leak',
         ('T205M.lean', 'end T205M',
          'private axiom cheat : False\n\ntheorem leak : (0 : ℕ) = 1 := cheat.elim\n\nend T205M')),
        ('swapped-arguments', 'builder', False, 'compile failed or warned: support',
         ('T205M.lean', 'unique_rank_cross_comparable hs hu ha hb)', 'unique_rank_cross_comparable hs hu hb ha)')),
        ('upward-closure-definition', 'builder', False, 'compile failed or warned: support',
         ('T205M.lean', ideal_def, '∀ ⦃x y : α⦄, y ∈ s → y ≤ x → x ∈ s')),
        ('mathlib-pin', 'builder', False, 'dependency pin mismatch: mathlib',
         ('lake-manifest.json', '"rev": "' + MATHLIB, '"rev": "' + '0' * 40)),
        ('hidden-conclusion-builder', 'builder', True, 'PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS',
         ('T205M.lean', no_cut_sig, no_cut_sig + '    (_h2 : ∃ s t : Finset α, IsIdeal s ∧ IsIdeal t ∧\n'
          '      s.card = r ∧ t.card = r ∧ s ≠ t)\n')),
        ('hidden-conclusion-independent', 'independent', False, 'Independent.lean:',
         ('T205M.lean', no_cut_sig, no_cut_sig + '    (_h2 : ∃ s t : Finset α, IsIdeal s ∧ IsIdeal t ∧\n'
          '      s.card = r ∧ t.card = r ∧ s ≠ t)\n')),
    ]
    results = []
    for name, kind, accept, reason, (target, old, new) in cases:
        dest = base / name
        shutil.copytree(PACKET, dest)
        mutate(dest / target, old, new)
        if kind == 'builder':
            code, text = run_builder(dest, base / (name + '-out'))
            accepted = code == 0
        else:
            build = base / (name + '-build')
            build.mkdir()
            for f in ['T205M.lean', 'Controls.lean']:
                shutil.copyfile(dest / f, build / f)
            shutil.copyfile(REVIEW / 'Independent.lean', build / 'Independent.lean')
            steps = compile_chain(build, [('T205M.lean', True), ('Controls.lean', True),
                                          ('Independent.lean', False)])
            text = ''.join(s['output'] for s in steps)
            accepted = len(steps) == 3 and all(s['exit_code'] == 0 for s in steps)
            if name == 'hidden-conclusion-independent':
                require(steps[0]['exit_code'] == 0 and steps[1]['exit_code'] == 0,
                        'author modules must still compile in hidden-conclusion control')
                require(re.search(r'Independent\.lean:\d+:\d+: error', text), 'pin did not reject')
        require(accepted == accept and reason in text,
                'control %s: accepted=%s\n%s' % (name, accepted, text[-3000:]))
        require(authenticate(PACKET)['manifest_sha256'] == ANCHOR, 'packet changed during controls')
        results.append({'case': name, 'checker': kind, 'accepted': accepted, 'expected_reason': reason})
    return results


if __name__ == '__main__':
    main()
