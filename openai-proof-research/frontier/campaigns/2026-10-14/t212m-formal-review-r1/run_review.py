#!/usr/bin/env python3
"""T212M scoped formal review r1 execution; MIT, reviewer-written.

Adapted from ../t205m-formal-review-r1/run_review.py (reviewed helper), with the
packet anchor, declaration lists, input bindings and mutation cases replaced for
T212M. Writes only inside this review directory and new /var/tmp directories.
The frozen packet and the shared dependency cache are read only; the cache is
fingerprinted before and after. No mathematical verdict is produced here.
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

ANCHOR = 'cc09818fed56aa44deda1f8fb9baf6d018bf6d4c3f8317f7bb6612f31624ce00'
SOURCE_SHA = {'T212M.lean': '9fbbbbc18a2706c993a5a9aefc278127c93cb7ff3a0d0bbb2376f567c3db8a8c',
              'Controls.lean': '0b9ae5012cc98c6bd9a90da71031f890ae25515ccd919f548c2c1ba8263ad9ee'}
AUTHOR_MANIFEST = '26a78331dfff175abd747c1b4212e48f5c9b24d703702d0474549dbd2eaf9566'
AUTHOR_CANDIDATE = 'a4fa6e4386808a3a864cb4d0c3cfe064e891f1a699bc0094cd5837d07f8dab55'
USE_SITE = 'label-stability-interface.md'
REVIEW = Path(__file__).resolve().parent
CAMPAIGN = REVIEW.parent
PACKET = CAMPAIGN / 't212m-formal-v1'
AUTHOR = CAMPAIGN / 'fresh-analytic-discovery-r74'
CACHE = CAMPAIGN / 'formal/.lake/packages'
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
LEAN_COMMIT = '5045d0056413266e57c625dcd7c365b10e377c52'
MATHLIB = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
SUPPORT = ['changeBudget', 'finite_cost_change', 'walkCost', 'walkCost_append', 'walk_cost_change',
           'walk_cost_unchanged', 'distance_dominated_by_cost', 'detour_barrier',
           'late_segment_minimizes', 'walkCost_nonneg', 'calibrated_segment_avoids',
           'ray_tail_stable', 'bypass_cost_le', 'ray_tail_stable_all_walks']
CONTROLS = ['lineDistance', 'lineWeight', 'changedEdges', 'newWeight', 'segment', 'line_triangle',
            'line_dominates', 'late_segment_example', 'repeatedEdge',
            'repeated_edge_breaks_single_budget', 'earlySegment', 'shortcut',
            'early_segment_is_old_minimal', 'early_segment_unchanged',
            'without_lateness_minimality_fails', 'newWeight_nonneg', 'late_segment_all_walks']
AUDITED = ['T212M.' + n for n in SUPPORT] + ['T212MControls.' + n for n in CONTROLS]
# Every non-audited constant the elaborator emits into the two modules.
AUXILIARY = {
    'T212M': ['T212M.late_segment_minimizes._simp_1_1', 'T212M.late_segment_minimizes._simp_1_2',
              'T212M.walkCost.eq_1'],
    'Controls': ['T212M.changeBudget.eq_1'] + ['T212MControls.%s.eq_1' % n for n in
                 ['changedEdges', 'earlySegment', 'lineDistance', 'lineWeight', 'newWeight',
                  'repeatedEdge', 'segment', 'shortcut']]
                + ['T212MControls.%s._proof_1' % n for n in
                   ['changedEdges', 'earlySegment', 'lineWeight', 'newWeight', 'repeatedEdge',
                    'segment', 'shortcut']] + ['T212MControls.repeatedEdge._proof_2'],
}
FORBIDDEN = re.compile(r'\b(?:sorry|admit|unsafe|native_decide|axiom|opaque|implemented_by|extern'
                       r'|set_option|macro|elab|syntax|instance|attribute)\b|@\[')
REVIEWER_FORBIDDEN = re.compile(r'\b(?:sorry|admit|unsafe|native_decide|implemented_by|extern'
                                r'|set_option)\b|^\s*(?:private\s+|protected\s+)?axiom\s', re.M)
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
    for rel, digest in SOURCE_SHA.items():
        require(files[rel]['sha256'] == digest, 'dispatch source mismatch ' + rel)
    binding = json.loads((root / 'inputs/binding.json').read_text())
    require(binding['author_manifest'] == AUTHOR_MANIFEST and binding['author_candidate'] == AUTHOR_CANDIDATE
            and binding['formal_source'] == SOURCE_SHA['T212M.lean']
            and binding['controls'] == SOURCE_SHA['Controls.lean']
            and binding['full_theorem_formalized'] is False, 'binding mismatch')
    return {'manifest_sha256': ANCHOR, 'files': len(files), 'directories': sorted(dirs)}


def authenticate_author():
    raw = (AUTHOR / 'manifest.json').read_bytes()
    require(sha(raw) == AUTHOR_MANIFEST, 'author manifest anchor mismatch')
    entries = json.loads(raw)['files']
    out = {}
    for rel in ['candidate-proof.md', USE_SITE]:
        data = (AUTHOR / rel).read_bytes()
        require(sha(data) == entries[rel]['sha256'], 'author file mismatch ' + rel)
        out[rel] = sha(data)
    require(out['candidate-proof.md'] == AUTHOR_CANDIDATE, 'candidate mismatch')
    text = (AUTHOR / USE_SITE).read_text()
    require('## Tail existence under any finite metric change' in text
            and 'T_s(a,b)+2T_s(x,a)-2C-Delta' in text, 'use-site text not found')
    return {'author_manifest_sha256': AUTHOR_MANIFEST, 'files': out}


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
    found, untracked = {}, {}
    for entry in lock['packages']:
        dep = CACHE / entry['name']
        head = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], text=True, env=ENV).strip()
        dirty = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain', '--untracked-files=no'],
                                        text=True, env=ENV)
        extra = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain', '--untracked-files=all'],
                                        text=True, env=ENV)
        require(head == entry['rev'] and not dirty.strip(), 'pin or cleanliness failure ' + entry['name'])
        lean_extra = [l for l in extra.splitlines() if l.endswith('.lean')]
        require(not lean_extra, 'untracked Lean source in dependency ' + entry['name'])
        found[entry['name']] = head
        untracked[entry['name']] = len(extra.splitlines())
    require(len(found) == 9 and found['mathlib'] == MATHLIB, 'expected nine pins with mathlib')
    version = subprocess.check_output([str(LEAN), '--version'], text=True).strip()
    require('4.34.1' in version and LEAN_COMMIT in version, 'wrong Lean')
    return {'dependencies': found, 'untracked_nonignored_entries': untracked,
            'lean_version': version, 'lean_sha256': sha(LEAN.read_bytes())}


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


def independent(build_dir, sources_root):
    build_dir.mkdir()
    for name in ['T212M.lean', 'Controls.lean']:
        shutil.copyfile(sources_root / name, build_dir / name)
    shutil.copyfile(REVIEW / 'Independent.lean', build_dir / 'Independent.lean')
    return compile_chain(build_dir, [('T212M.lean', True), ('Controls.lean', True), ('Independent.lean', False)])


def main():
    work = Path(tempfile.mkdtemp(prefix='t212m-formal-review-r1-', dir='/var/tmp'))
    record = {'status': 'RUNNING', 'work_directory': str(work), 'anchor': ANCHOR}
    record['authentication_before'] = authenticate(PACKET)
    record['author_binding'] = authenticate_author()
    record['pins_before'] = pins()
    record['cache_before'] = cache_fingerprint()

    code, text = run_builder(PACKET, work / 'builder-output', defaults=True)
    require(code == 0 and 'PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS' in text
            and 'Support declarations: 14' in text and 'Control declarations: 17' in text, 'builder failed')
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
    require(fresh['lean_binary_sha256'] == record['pins_before']['lean_sha256'], 'compiler hash')
    for name in ['Checks.lean', 'types-axioms.log', 'support.log', 'controls.log']:
        require((copy / name).read_bytes() == (PACKET / 'validation' / name).read_bytes(),
                'fresh log differs: ' + name)
    require(sum(fresh['declarations'].values(), []) == AUDITED, 'audited set or order differs')
    for name, axioms in fresh['kernel_dependencies'].items():
        require(set(axioms) <= STANDARD, 'axiom ' + name)
    log = (copy / 'types-axioms.log').read_text()
    for name in AUDITED:
        require(re.search(r'^@?' + re.escape(name) + r' :', log, re.M), 'missing #check ' + name)
    require(not re.search(r'sorryAx|\bsorry\b', log), 'sorry in types log')
    record['builder'] = {'exit_code': code, 'receipt_sha256': sha((copy / 'receipt.json').read_bytes()),
                         'logs_identical_to_frozen_validation': True, 'audited_declarations': len(AUDITED)}

    for name in ['T212M.lean', 'Controls.lean']:
        require(not FORBIDDEN.search((PACKET / name).read_text()), 'forbidden token ' + name)
    require(not REVIEWER_FORBIDDEN.search((REVIEW / 'Independent.lean').read_text()),
            'forbidden token Independent.lean')
    steps = independent(work / 'independent', PACKET)
    logs = REVIEW / 'independent-logs'
    if logs.exists():
        shutil.rmtree(logs)
    logs.mkdir()
    for step in steps:
        (logs / (step['file'] + '.log')).write_text(step['output'])
    require(len(steps) == 3 and all(s['exit_code'] == 0 for s in steps), 'independent compile failed')
    require(not any(re.search(r'\b(?:error|warning):', s['output']) for s in steps), 'independent warnings')
    inv = steps[2]['output']
    require('INDEPENDENT_INVENTORY_PASS' in inv and 'MODULE T212M constants=17' in inv
            and 'MODULE Controls constants=34' in inv, 'independent inventory failed')
    sections = re.split(r'^MODULE |^REVIEWER ', inv, flags=re.M)
    listed = {}
    for sec in sections[1:3]:
        mod = sec.split(' ', 1)[0]
        listed[mod] = re.findall(r'^  (\S+) kind=(\w+)((?: instance)?)((?: internal)?)((?: UNSAFE)?) '
                                 r'axioms=\[([^\]]*)\]', sec, re.M)
    names = {m: sorted(n for n, *_ in rows) for m, rows in listed.items()}
    expected = {'T212M': sorted(['T212M.' + n for n in SUPPORT] + AUXILIARY['T212M']),
                'Controls': sorted(['T212MControls.' + n for n in CONTROLS] + AUXILIARY['Controls'])}
    require(names == expected, 'module constant inventory differs: %s' % names)
    require(not any(r[2] or r[4] for rows in listed.values() for r in rows), 'instance or unsafe constant')
    require(all(r[1] in ('def', 'theorem') for rows in listed.values() for r in rows), 'unexpected kind')
    record['independent'] = {
        'constants_T212M_module': 17, 'constants_Controls_module': 34,
        'auxiliary_constants': AUXILIARY, 'instances': [], 'unsafe': [], 'all_axioms_standard': True,
        'reviewer_constants': int(re.search(r'REVIEWER constants=(\d+)', inv).group(1)),
        'log_sha256': sha(inv.encode())}

    r = subprocess.run(['python3', '-B', str(PACKET / 'verify.py'), '--anchor', ANCHOR],
                       cwd='/var/tmp', env=ENV, capture_output=True, text=True)
    require(r.returncode == 0 and 'PASS_IDENTITY_ONLY' in r.stdout, 'packet verify.py failed')
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
    require(record['pins_after'] == record['pins_before'], 'pins changed')
    record['authentication_after'] = authenticate(PACKET)
    record['status'] = 'EXECUTION_COMPLETE'
    (REVIEW / 'execution.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print(record['status'], work)


def mutation_controls(work):
    hpres = ('    (C : ℝ) (hregion : ∀ e ∈ F, ∃ c, c ∈ e ∧ d x c ≤ C) :\n'
             '    ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, i ≤ j →\n'
             '      ∀ p : G.Walk (ray i) (ray j), walkCost')
    hidden = hpres.replace(') :\n', ')\n    (_hpres : ∀ i j (p : G.Walk (ray i) (ray j)),\n'
                           '      walkCost w\' (segments i j) ≤ walkCost w\' p) :\n', 1)
    weak_old = ('      ∀ p : G.Walk (ray i) (ray j), walkCost w\' (segments i j) ≤ walkCost w\' p := by\n'
                '  obtain ⟨N, hN⟩ := ray_tail_stable d hsym htri w w\' hw F hoff hdom x ray\n'
                '    segments hsegments hcal hescape C hregion\n'
                '  refine ⟨N, ?_⟩\n'
                '  intro i hi j hij p\n')
    weak_new = weak_old.replace('(ray j), walkCost', '(ray j), p.edges.Nodup → walkCost').replace(
        'intro i hi j hij p\n', 'intro i hi j hij p _\n')
    cases = [
        ('sorry-proof', 'builder', False, 'forbidden proof escape: T212M.lean',
         ('T212M.lean', '    exact add_nonneg (hw _) ih', '    sorry')),
        ('declared-axiom', 'builder', False, 'forbidden proof escape: T212M.lean',
         ('T212M.lean', 'end T212M', 'axiom cheat : False\n\nend T212M')),
        ('private-axiom-dependency', 'builder', False, 'unapproved axiom dependency: T212M.leak',
         ('T212M.lean', 'end T212M',
          'private axiom cheat : False\n\ntheorem leak : (0 : ℕ) = 1 := cheat.elim\n\nend T212M')),
        ('controls-sorry', 'builder', False, 'forbidden proof escape: Controls.lean',
         ('Controls.lean', '    subst e\n    decide\n', '    subst e\n    sorry\n')),
        ('budget-without-abs', 'builder', False, 'compile failed or warned: support',
         ('T212M.lean', "∑ e ∈ F, |w' e - w e|", "∑ e ∈ F, (w' e - w e)")),
        ('drop-new-nonneg', 'builder', False, 'compile failed or warned: support',
         ('T212M.lean', "(hw : ∀ e, 0 ≤ w e) (hw' : ∀ e, 0 ≤ w' e)", '(hw : ∀ e, 0 ≤ w e)')),
        ('drop-lateness', 'builder', False, 'compile failed or warned: support',
         ('T212M.lean', '    (hlate : C + changeBudget F w w\' / 2 < d x a)\n', '')),
        ('mathlib-pin', 'builder', False, 'dependency pin mismatch: mathlib',
         ('lake-manifest.json', '"rev": "' + MATHLIB, '"rev": "' + '0' * 40)),
        ('hidden-conclusion-builder', 'builder', True, 'PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS',
         ('T212M.lean', hpres, hidden)),
        ('hidden-conclusion-independent', 'independent', False, 'Independent.lean:',
         ('T212M.lean', hpres, hidden)),
        ('weakened-conclusion-builder', 'builder', True, 'PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS',
         ('T212M.lean', weak_old, weak_new)),
        ('weakened-conclusion-independent', 'independent', False, 'Independent.lean:',
         ('T212M.lean', weak_old, weak_new)),
    ]
    results = []
    for name, kind, accept, reason, (target, old, new) in cases:
        dest = work / 'mutations' / name / 't212m-formal-v1'
        shutil.copytree(PACKET, dest)
        path = dest / target
        data = path.read_text()
        require(data.count(old) == 1, 'mutation anchor not unique: ' + name)
        path.write_text(data.replace(old, new))
        if kind == 'builder':
            code, text = run_builder(dest, work / 'mutations' / name / 'out')
            accepted = code == 0
        else:
            steps = independent(work / 'mutations' / name / 'independent', dest)
            text = ''.join(s['output'] for s in steps)
            accepted = len(steps) == 3 and all(s['exit_code'] == 0 for s in steps)
            require(steps[0]['exit_code'] == 0 and steps[1]['exit_code'] == 0,
                    'author modules must still compile in ' + name)
            require(re.search(r'Independent\.lean:\d+:\d+: error', text), 'pin did not reject ' + name)
        require(accepted == accept and reason in text,
                'control %s: accepted=%s\n%s' % (name, accepted, text[-3000:]))
        require(authenticate(PACKET)['manifest_sha256'] == ANCHOR, 'packet changed during controls')
        results.append({'case': name, 'checker': kind, 'accepted': accepted, 'expected_reason': reason})
    return results


if __name__ == '__main__':
    main()
