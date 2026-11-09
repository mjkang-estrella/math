"""Portable strict replay of the MathDB 368807 Lean dossier.

    LEAN_BIN=/path/to/lean-4.34.1/bin LEAN_PACKAGES=/path/to/.lake/packages \
        python3 -I tools/replay.py OUT_DIR

Run from anywhere; the dossier root is the parent of this file's directory.  OUT_DIR must not exist.
Steps (every Lean call goes through tools/watchdog.py, one call at a time):
  1. pins: Lean version/commit, SHA-256 of lean and leanchecker, mathlib revision, package manifest;
  2. refuse any existing .olean/.ilean (or .lake) in the dossier; verify MANIFEST.json if present;
  3. byte identity of the 22 Lean modules with the pinned hashes; forbidden-token scan;
  4. strict builds `lean -j1 -DwarningAsError=true` in dependency order into a fresh OUT_DIR/build;
  5. leanchecker on every built module;
  6. full declaration audit (audit/Audit.lean), parsed and re-checked here;
  7. one positive and six negative controls;
  8. OUT_DIR/replay-receipt.json (all_ok true only if every step passed).
"""
import datetime, hashlib, json, os, re, shutil, subprocess, sys
from pathlib import Path

D = Path(__file__).resolve().parents[1]
WATCHDOG = D / 'tools' / 'watchdog.py'
PROOF_MODULES = ['ASEPData', 'ASEPCheck', 'ASEPCover'] + [f'ASEPCerts{k}' for k in range(12)] + \
    ['ASEPDefs', 'ASEPSound', 'ASEPVertex', 'ASEPBridge', 'ASEPMain', 'ASEPArcs']
HELPER_MODULES = ['PermOrder']          # frozen helper, not imported by any proof module
AUDIT_LIB = 'AuditLib'
PACKAGES = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible', 'proofwidgets', 'Qq']
FORBIDDEN = ['sorry', 'admit', 'axiom', 'unsafe', 'native_decide', 'ofReduceBool', 'ofReduceNat',
             'implemented_by', 'extern', 'partial', 'opaque', '#eval', 'run_cmd', 'elab', 'macro',
             'debug.skipKernelTC', 'Lean.trustCompiler']
CONTROLS = [  # (module, expected rc == 0?, required substring in output)
    ('PosControl', True, None),
    ('NegCertMutation', False, 'Tactic `decide` proved that the proposition'),
    ('NegTourSwap', False, 'Tactic `decide` proved that the proposition'),
    ('NegDropCut', False, 'Tactic `decide` proved that the proposition'),
    ('NegNoTightCut', False, 'Tactic `decide` proved that the proposition'),
    ('NegSorry', False, 'declaration uses `sorry`'),
    ('NegAxiom', False, 'ASEPAUDIT FAIL neg_uses_cheat: nonstandard axioms [neg_cheat]'),
]
ENDPOINTS = ['ASEP.arc_counterexample', 'ASEP.arc_neighborhood_tour_conjecture_false', 'ASEP.counterexample',
             'ASEP.neighborhood_tour_conjecture_false', 'ASEP.segment_not_face', 'ASEP.segment_not_exposed']
STD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED_NUM_DECLS = 300          # stated in the paper
EXPECTED_HELPERS = ['ASEP.digs._unsafe_rec', 'ASEP.triples._unsafe_rec']


def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def strip_lean(src):
    """Remove (nested) block comments, line comments and string literals."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and src.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif src.startswith('--', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append('""')
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)


def scan(path):
    code = strip_lean(path.read_text())
    hits = {}
    for tok in FORBIDDEN:
        pat = (r'(?<![\w.])' if tok[0].isalnum() else '') + re.escape(tok) + r'(?![\w])'
        found = [code.count('\n', 0, m.start()) + 1 for m in re.finditer(pat, code)]
        if found:
            hits[tok] = found
    # `#print axioms` lines are allowed; they are reported separately
    return hits


def main():
    out = Path(sys.argv[1]).resolve()
    lean_bin = Path(os.environ['LEAN_BIN']).resolve()
    pkgs = Path(os.environ['LEAN_PACKAGES']).resolve()
    if out.exists():
        sys.exit(f'refusing to reuse existing output directory {out}')
    pins = json.loads((D / 'pins.json').read_text())
    steps, problems = [], []

    def need(cond, what):
        steps.append({'check': what, 'ok': bool(cond)})
        if not cond:
            problems.append(what)
        return cond

    # 2. no prebuilt artefacts in the dossier; manifest
    stale = [str(p.relative_to(D)) for p in D.rglob('*') if p.suffix in ('.olean', '.ilean', '.c') or p.name == '.lake']
    if stale:
        sys.exit(f'refusing: existing build artefacts in dossier: {stale[:5]}')
    man = D / 'MANIFEST.json'
    if man.exists():
        m = json.loads(man.read_text())
        listed = set(m['files'])
        present = {str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and p.name != 'MANIFEST.json'
                   and '__pycache__' not in p.parts}
        need(listed == present, 'MANIFEST.json lists exactly the dossier files')
        need(all(sha(D / k) == v for k, v in m['files'].items() if (D / k).exists()), 'MANIFEST.json hashes match')
    else:
        need(False, 'MANIFEST.json present')

    out.mkdir(parents=True)
    src, build, logs, home = out / 'src', out / 'build', out / 'logs', out / 'home'
    for p in (src, build, logs, home):
        p.mkdir()

    # 1. pins
    lean, checker = lean_bin / 'lean', lean_bin / 'leanchecker'
    need(sha(lean) == pins['lean_sha256'], 'lean binary SHA-256 pinned')
    need(sha(checker) == pins['leanchecker_sha256'], 'leanchecker binary SHA-256 pinned')
    libs = [pkgs / p / '.lake' / 'build' / 'lib' / 'lean' for p in PACKAGES]
    need(all(l.is_dir() for l in libs), 'pinned package libraries present')
    up = pkgs.parent.parent / 'lake-manifest.json'
    need(sha(D / 'upstream-lake-manifest.json') == pins['lake_manifest_sha256'], 'dossier lake manifest pinned')
    if up.exists():
        need(sha(up) == pins['lake_manifest_sha256'], 'package lake-manifest.json matches pin')
    manifest = json.loads((D / 'upstream-lake-manifest.json').read_text())
    revs = {p['name']: p['rev'] for p in manifest['packages']}
    need(revs.get('mathlib') == pins['mathlib_rev'], 'mathlib revision in manifest')
    head = pkgs / 'mathlib' / '.git' / 'HEAD'
    if head.is_file():   # a plain file read; no git command is run
        need(head.read_text().strip() == pins['mathlib_rev'], 'mathlib checkout HEAD file equals pinned revision')

    env = {'PATH': f'{lean_bin}:/usr/bin:/bin', 'HOME': str(home), 'LANG': 'C.UTF-8',
           'LEAN_PATH': ':'.join(map(str, libs + [build])), 'MALLOC_ARENA_MAX': '2'}
    for k in ('XDG_RUNTIME_DIR', 'DBUS_SESSION_BUS_ADDRESS', 'ASEP_NO_SCOPE'):
        if k in os.environ:
            env[k] = os.environ[k]
    calls = []

    def run(name, args):
        rec = logs / f'{name}.watch.json'
        so, se = logs / f'{name}.stdout', logs / f'{name}.stderr'
        subprocess.run([sys.executable, '-I', '-B', str(WATCHDOG), str(rec), str(so), str(se), str(src), '--'] + args,
                       env=env)
        r = json.loads(rec.read_text())
        r['name'] = name
        r['stdout_sha256'], r['stderr_sha256'] = sha(so), sha(se)
        r['output'] = so.read_text(errors='replace') + se.read_text(errors='replace')
        calls.append({k: v for k, v in r.items() if k != 'output'})
        return r

    v = run('lean-version', [str(lean), '--version'])
    need(v['rc'] == 0 and pins['lean_commit'] in v['output'] and '4.34.1' in v['output'], 'Lean 4.34.1 at pinned commit')

    # 3. byte identity and scan
    ident = {}
    for f in sorted((D / 'lean').glob('*.lean')):
        ident[f.name] = sha(f)
    need(ident == pins['lean_module_sha256'], 'Lean modules byte-identical to expanded-corpus-r96/lean')
    scans = {m: scan(D / 'lean' / f'{m}.lean') for m in PROOF_MODULES + HELPER_MODULES}
    need(all(not scans[m] for m in PROOF_MODULES), 'forbidden-token scan of the 21 proof modules clean')
    need(set(scans['PermOrder']) <= {'#eval'}, 'PermOrder helper: only #eval (file export, not imported by proofs)')
    imports = {m: re.findall(r'^import (\S+)', (D / 'lean' / f'{m}.lean').read_text(), re.M) for m in PROOF_MODULES}
    need(all('PermOrder' not in v for v in imports.values()), 'no proof module imports PermOrder')
    for f in list((D / 'lean').glob('*.lean')) + list((D / 'audit').glob('*.lean')) + list((D / 'negative').glob('*.lean')):
        shutil.copy2(f, src / f.name)

    # 4. strict builds
    for mname in PROOF_MODULES + HELPER_MODULES + [AUDIT_LIB]:
        assert not (build / f'{mname}.olean').exists()
        r = run(f'build-{mname}', [str(lean), '-j1', '-DwarningAsError=true', '-o', str(build / f'{mname}.olean'),
                                   '-i', str(build / f'{mname}.ilean'), f'{mname}.lean'])
        need(r['rc'] == 0 and r['killed'] is None, f'strict build {mname}')
        if r['rc'] != 0:
            break
    perm = src / 'perm-order.txt'
    if perm.exists():
        need(sha(perm) == pins['perm_order_txt_sha256'], 'PermOrder export equals frozen perm-order.txt')
    print_axioms = {}
    for mname in ('ASEPMain', 'ASEPArcs'):
        so = (logs / f'build-{mname}.stdout').read_text() if (logs / f'build-{mname}.stdout').exists() else ''
        print_axioms[mname] = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", so)
    pa = [(n, {a.strip() for a in axs.split(',')}) for m in print_axioms.values() for n, axs in m]
    need(len(pa) == 5 and all(a <= STD_AXIOMS for _, a in pa), 'in-module #print axioms: 5 endpoints, standard axioms only')

    # 5. leanchecker
    for mname in PROOF_MODULES + HELPER_MODULES:
        r = run(f'leanchecker-{mname}', [str(checker), mname])
        need(r['rc'] == 0 and r['killed'] is None, f'leanchecker {mname}')

    # 6. audit
    r = run('audit', [str(lean), '-j1', '-DwarningAsError=true', 'Audit.lean'])
    need(r['rc'] == 0 and r['killed'] is None, 'audit module compiles (all in-Lean audit assertions hold)')
    decls = [json.loads(l.split('ASEPAUDIT-DECL ', 1)[1]) for l in r['output'].splitlines() if 'ASEPAUDIT-DECL ' in l]
    summ = [json.loads(l.split('ASEPAUDIT-SUMMARY ', 1)[1]) for l in r['output'].splitlines() if 'ASEPAUDIT-SUMMARY ' in l]
    oks = re.findall(r'ASEPAUDIT OK (\S+): #?\[([^\]]*)\]', r['output'])
    (out / 'audit').mkdir()
    (out / 'audit' / 'declarations.jsonl').write_text(''.join(json.dumps(d, sort_keys=True) + '\n' for d in decls))
    audit = {}
    if need(len(summ) == 1, 'audit summary present'):
        s = summ[0]
        helpers = s['unsafe_rec_helpers']
        names = [d['name'] for d in decls]
        mods = {d['module'] for d in decls}
        defthm = [d for d in decls if d['kind'] in ('def', 'theorem')]
        need(len(names) == len(set(names)) == s['num_local_constants'], 'audit: one record per local constant')
        need(len(names) == EXPECTED_NUM_DECLS, f'audit: {EXPECTED_NUM_DECLS} local constants as stated in the paper')
        need(sorted(helpers) == EXPECTED_HELPERS, 'audit: exactly the two expected _unsafe_rec helpers')
        need(mods <= set(PROOF_MODULES + HELPER_MODULES) and set(PROOF_MODULES) <= mods, 'audit: modules covered')
        need(all(d['value?_allowOpaque'] for d in defthm), 'audit: every def/theorem has a body (value? with allowOpaque := true)')
        need(all(d['value?'] for d in defthm if d['kind'] == 'def'), 'audit: every def has a body (plain value?)')
        need(all(d['clean'] for d in decls if not d['unsafe_rec_helper']), 'audit: every non-helper declaration clean')
        need(all(set(d['collectAxioms']) <= STD_AXIOMS for d in decls), 'audit: collectAxioms standard for every declaration')
        need(all(d['unsafe'] or d['partial'] for d in decls if d['unsafe_rec_helper']),
             'audit: _unsafe_rec helpers are flagged (partial or unsafe)')
        need(not [d for d in decls if (d['unsafe'] or d['partial']) and not d['unsafe_rec_helper']],
             'audit: no other unsafe/partial declaration')
        need(set(s['all_locals_walk_axioms']) <= STD_AXIOMS, 'audit: uncached walk axioms standard')
        eps = {e['endpoint']: e for e in s['endpoints']}
        need(set(eps) == set(ENDPOINTS), 'audit: all six endpoints present')
        for e in ENDPOINTS:
            x = eps.get(e, {})
            need(x.get('ok') and not x.get('local_unsafe_rec_helpers_reached') and not x.get('unsafe_rec_in_closure')
                 and set(x.get('walk_axioms', [])) <= STD_AXIOMS and set(x.get('collectAxioms', [])) <= STD_AXIOMS,
                 f'audit: endpoint {e} closure standard and free of _unsafe_rec helpers')
        need(not s['failures'], 'audit: no in-Lean failures')
        need(sorted(n for n, _ in oks) == sorted(ENDPOINTS), 'audit: #assert_std_axioms passed for all six endpoints')
        audit = {'summary': s, 'num_declarations': len(decls), 'unsafe_rec_helpers': helpers,
                 'declarations_sha256': sha(out / 'audit' / 'declarations.jsonl'),
                 'kinds': {k: sum(1 for d in decls if d['kind'] == k) for k in sorted({d['kind'] for d in decls})}}
        (out / 'audit' / 'summary.json').write_text(json.dumps(s, indent=1))

    # 7. controls
    ctl = []
    for mname, should_pass, needle in CONTROLS:
        r = run(f'control-{mname}', [str(lean), '-j1', '-DwarningAsError=true', f'{mname}.lean'])
        good = (r['rc'] == 0) if should_pass else (r['rc'] not in (0, None) and r['killed'] is None
                                                   and needle in r['output'] and 'error' in r['output'])
        ctl.append({'module': mname, 'expected': 'success' if should_pass else 'failure', 'rc': r['rc'],
                    'needle': needle, 'as_expected': good})
        need(good, f'control {mname} behaves as expected')

    caps_ok = all(c['killed'] is None and c['cpu_seconds'] <= 120 and c['wall_seconds'] <= 140
                  and c['peak_sampled_rss_bytes'] <= 6 * 1024 ** 3 for c in calls)
    need(caps_ok, 'every call within caps (no kill, CPU <= 120 s, wall <= 140 s, sampled RSS <= 6 GiB)')
    receipt = {
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'dossier': str(D), 'out': str(out),
        'lean_bin': str(lean_bin), 'lean_packages': str(pkgs), 'pins': pins, 'environment': env,
        'module_order': PROOF_MODULES + HELPER_MODULES + [AUDIT_LIB], 'scan': scans,
        'print_axioms_in_modules': print_axioms, 'audit': audit, 'controls': ctl, 'calls': calls,
        'num_lean_calls': len(calls),
        'max_cpu_seconds': max(c['cpu_seconds'] for c in calls), 'max_wall_seconds': max(c['wall_seconds'] for c in calls),
        'peak_sampled_rss_bytes': max(c['peak_sampled_rss_bytes'] for c in calls),
        'peak_sampled_private_rss_bytes': max(c['peak_sampled_private_rss_bytes'] for c in calls),
        'steps': steps, 'problems': problems, 'all_ok': not problems,
    }
    (out / 'replay-receipt.json').write_text(json.dumps(receipt, indent=1))
    print(json.dumps({'all_ok': not problems, 'problems': problems, 'calls': len(calls),
                      'peak_rss': receipt['peak_sampled_rss_bytes'], 'max_cpu': receipt['max_cpu_seconds']}))
    sys.exit(0 if not problems else 1)


if __name__ == '__main__':
    main()
