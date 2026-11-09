#!/usr/bin/env python3
"""Bounded, checkpointed nd-sym continuation. All writes are confined to sym2/."""
import sys
sys.dont_write_bytecode = True
import argparse
import collections
import concurrent.futures
import hashlib
import itertools
import json
import math
import pathlib
import signal
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
HD = HERE.parent
ROOT = HD.parent.parent
sys.path.insert(0, str(HERE))
from gen_sym import Generator, Budget, valuation
from audit_coverage import cover, finite_scan


def read(p):
    return json.loads(pathlib.Path(p).read_text())


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def save(p, obj):
    p = pathlib.Path(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(p.suffix + '.tmp')
    tmp.write_text(json.dumps(obj, indent=1) + '\n')
    tmp.replace(p)


def reconcile():
    sources = [HD / stage / 'results_t14112.json' for stage in ('codex', 'codex3a', 'codex3b')]
    sources += [HD / 'sym/summary.json']
    baseline = read(sources[0])
    closed = set(read(sources[-1])['closed'])
    provenance = collections.defaultdict(list)
    for p in sources[:3]:
        for k, rec in read(p).items():
            assert k in baseline and rec['far'] == baseline[k]['far']
            if rec['status'] == 'CLOSED':
                closed.add(k)
                provenance[k].append(str(p.relative_to(ROOT)))
    for k in read(sources[-1])['closed']:
        provenance[k].append('verification/highdim/sym/summary.json')
    remaining = {k: v for k, v in baseline.items() if k not in closed}
    bydim = {str(d): sorted(k for k, v in remaining.items() if len(v['far']) + 1 == d)
             for d in sorted({len(v['far']) + 1 for v in remaining.values()})}
    assert set(read(sources[-1])['BUDGET']) == {k for k, v in remaining.items() if 6 <= len(v['far']) + 1 <= 8}
    t32sources = [HD / stage / 'results_t32.json' for stage in ('codex', 'codex3a')]
    b32 = read(t32sources[0])
    c32 = {k for p in t32sources for k, v in read(p).items() if v['status'] == 'CLOSED'}
    open32 = {k: v for k, v in b32.items() if k not in c32}
    assert set(open32) == {'11|9,9,9'}
    jobs = {'14112:' + k: dict(v, target=14112, key=k) for k, v in remaining.items()}
    jobs.update({'32:' + k: dict(v, target=32, key=k) for k, v in open32.items()})
    output = {'label': 'COMPUTED', 'baseline_count': len(baseline), 'previously_closed': len(closed),
              'open_14112_count': len(remaining), 'open_by_dimension': bydim,
              'open_32': sorted(open32), 'configurations': jobs,
              'source_hashes': {str(p.relative_to(ROOT)): sha(p) for p in sources + t32sources},
              'previous_closure_provenance': dict(provenance)}
    save(HERE / 'assignment.json', output)
    print(json.dumps({k: output[k] for k in ('baseline_count', 'previously_closed', 'open_14112_count', 'open_32')}))
    print('open dimensions', {d: len(keys) for d, keys in bydim.items()})


def slices(K0, coefs, extra_floor=0):
    todo = [(K0, tuple(sorted(coefs)), (3,) * len(coefs))]
    seen, result = set(), set()
    while todo:
        K, cs, floors = todo.pop()
        state = (K, cs, floors)
        if state in seen:
            continue
        seen.add(state)
        if len(seen) > 200000:
            raise Budget('slice enumeration')
        floor = max(3, valuation(K, 2) + 1 + extra_floor)
        bad = next((i for i, x in enumerate(floors) if x < floor), None)
        if bad is None:
            result.add((K, cs, floor))
            continue
        for q in range(floors[bad], floor):
            todo.append((K + cs[bad] * 10**q, cs[:bad] + cs[bad + 1:], floors[:bad] + floors[bad + 1:]))
        todo.append((K, cs, floors[:bad] + (floor,) + floors[bad + 1:]))
    return sorted(result, key=lambda z: (-len(z[1]), z[0], z[2]))


LIBRARY = {}


def library():
    global LIBRARY
    LIBRARY = {}
    previous = HD / 'sym/standalone_checks.json'
    for f, rec in read(previous)['files'].items():
        if rec['result'] != 'PASS' or rec['check']['scope'] != 'full':
            continue
        p = (previous.parent / f).resolve()
        with p.open() as stream:
            m = json.loads(next(stream))
        cs = tuple(c for c, n in m['groups'] for _ in range(n))
        LIBRARY[(m['K'], cs, m['qmin'])] = (str(p), rec['sha256'])
    for p in sorted((HERE / 'certs').rglob('*.jsonl')):
        with p.open() as stream:
            m = json.loads(next(stream))
        cs = tuple(c for c, n in m['groups'] for _ in range(n))
        LIBRARY[(m['K'], cs, m['qmin'])] = (str(p), sha(p))


def alarm(signum, frame):
    raise Budget('wall alarm')


def search_worker(args):
    name, rec, seconds, lifts, schedule, stage, extra_floor, pin_digits = args
    signal.signal(signal.SIGALRM, alarm)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    start = time.monotonic()
    out = {'name': name, 'key': rec['key'], 'target': rec['target'], 'dim': len(rec['far']) + 1,
           'stage': stage, 'status': 'BUDGET', 'jobs': []}
    g = None
    try:
        domains = slices(9 * rec['S_low'] - 1, rec['far'], extra_floor)
        out['slice_count'] = len(domains)
        out['finite_Lmax'] = max(q - 1 for K, cs, q in domains)
        for K, cs, q in domains:
            cached = LIBRARY.get((K, cs, q))
            fn = HERE / 'certs' / stage / ('K%d_q%d_c%s.jsonl' % (K, q, '_'.join(map(str, cs)) or 'none'))
            if cached:
                fp = pathlib.Path(cached[0])
                assert sha(fp) == cached[1], 'changed inherited certificate'
                out['jobs'].append({'K': K, 'coefs': cs, 'qmin': q, 'file': str(fp), 'sha256': cached[1], 'cached': True})
                continue
            if fn.exists():
                out['jobs'].append({'K': K, 'coefs': cs, 'qmin': q, 'file': str(fn), 'sha256': sha(fn), 'cached': True})
                continue
            g = Generator(cs, K, q, seconds=max(.001, seconds - (time.monotonic() - start)),
                          lifts=lifts, nodes=1000000, sumsets=True, pin_digits=pin_digits)
            g.run(schedule)
            g.write(fn, extra={'target': rec['target'], 'configuration': rec['key'], 'stage': stage})
            out['jobs'].append({'K': K, 'coefs': cs, 'qmin': q, 'file': str(fn), 'sha256': sha(fn),
                                'nodes': len(g.nodes), 'lifts': g.lifts, 'kills': dict(g.kills), 'trace': g.trace})
        out['status'] = 'COMPLETE_PENDING_CHECKS'
    except Exception as e:
        out['reason'] = repr(e)
        if not isinstance(e, Budget):
            out['status'] = 'FAIL'
        if g is not None:
            out['partial'] = {'nodes': len(g.nodes), 'lifts': g.lifts, 'kills': dict(g.kills), 'trace': g.trace, 'at': g.at}
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    out['seconds'] = round(time.monotonic() - start, 3)
    return out


def search(a):
    library()
    cfg = read(HERE / 'assignment.json')['configurations']
    completed = set()
    for p in HERE.glob('search_*.json'):
        completed.update(k for k, v in read(p).items() if v['status'] == 'COMPLETE_PENDING_CHECKS')
    if (HERE / 'summary.json').exists():
        completed.update(read(HERE / 'summary.json')['closed'])
    path = HERE / ('search_' + a.stage + '.json')
    results = read(path) if path.exists() else {}
    jobs = [(k, v, a.seconds, a.lifts, tuple(map(int, a.schedule.split(','))), a.stage, a.extra_floor, a.pin_digits)
            for k, v in sorted(cfg.items(), key=lambda kv: (len(kv[1]['far']), kv[0]))
            if a.mindim <= len(v['far']) + 1 <= a.maxdim and k not in completed and k not in results
            and (not a.key or k in a.key.split(';'))]
    save(HERE / ('input_' + a.stage + '.json'), {'seconds_per_configuration': a.seconds, 'lifts': a.lifts,
         'schedule': a.schedule, 'workers': a.workers, 'extra_floor': a.extra_floor, 'pin_digits': a.pin_digits,
         'keys': [j[0] for j in jobs], 'code_hashes': {f: sha(HERE / f) for f in ('gen_sym.py', 'check_sym.py', 'continue_sym2.py')}})
    print('jobs', len(jobs), 'seconds', a.seconds, 'workers', a.workers, flush=True)
    # A barrier between dimensions ensures the smaller configurations run first.
    with concurrent.futures.ProcessPoolExecutor(max_workers=a.workers) as pool:
        for dim in sorted({len(j[1]['far']) + 1 for j in jobs}):
            pending = {pool.submit(search_worker, j): j[0] for j in jobs if len(j[1]['far']) + 1 == dim}
            for f in concurrent.futures.as_completed(pending):
                k = pending[f]
                results[k] = f.result()
                save(path, results)
                print(k, results[k]['status'], results[k]['seconds'], 'done', len(results), flush=True)
    print('counts', dict(collections.Counter(v['status'] for v in results.values())), flush=True)


def check_worker(path):
    before = sha(path)
    start = time.monotonic()
    command = ['bash', '-c', 'ulimit -v 8000000; python3 -I "$@"', 'sym2-direct-check', str(HERE / 'check_sym.py'), str(path), '10']
    try:
        p = subprocess.run(command, text=True, capture_output=True, timeout=900)
        parsed = json.loads(p.stdout.strip().splitlines()[-1])
        assert p.returncode == 0 and parsed['result'] == 'PASS', (p.returncode, p.stderr[-1000:], parsed)
        assert sha(path) == before
        return {'result': 'PASS', 'sha256': before, 'command': command, 'check': parsed, 'seconds': round(time.monotonic() - start, 3)}
    except Exception as e:
        return {'result': 'FAIL', 'sha256': before, 'command': command, 'error': repr(e), 'seconds': round(time.monotonic() - start, 3)}


def checks(a):
    paths = set((HERE / 'certs').rglob('*.jsonl'))
    for p in HERE.glob('search_*.json'):
        for rec in read(p).values():
            paths.update(pathlib.Path(j['file']) for j in rec['jobs'])
    output = HERE / 'standalone_checks.json'
    ledger = read(output) if output.exists() else {'files': {}}
    ledger.update(checker_sha256=sha(HERE / 'check_sym.py'), brute_Lmax=10)
    todo = [p for p in sorted(paths) if str(p) not in ledger['files'] or ledger['files'][str(p)]['sha256'] != sha(p)]
    print('direct checks', len(todo), 'already checked', len(ledger['files']), flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
        pending = {pool.submit(check_worker, p): str(p) for p in todo}
        for fut in concurrent.futures.as_completed(pending):
            key = pending[fut]
            ledger['files'][key] = fut.result()
            save(output, ledger)
            print(len(ledger['files']), key, ledger['files'][key]['result'], flush=True)
    save(output, ledger)
    print('counts', dict(collections.Counter(v['result'] for v in ledger['files'].values())), flush=True)


def usage(path):
    with pathlib.Path(path).open() as stream:
        m = json.loads(next(stream))
        counts = collections.Counter()
        prime_ids = set()
        for line in stream:
            n = json.loads(line)
            if n['k'] == 'l' and 'sz' in n['x']:
                counts['exact_size_leaf'] += 1
            ps = n.get('rest', []) if n['k'] == 'i' else [n['x']['prime']] if 'prime' in n['x'] else []
            M = n.get('m2', n['m'])
            for p in ps:
                prime_ids.add(p)
                d = ORDERS[p]
                counts['aligned_prime_reference' if M % d == 0 else 'unaligned_sumset_reference'] += 1
    dependencies = []
    if prime_ids:
        dependencies.append('prime_coset')
        if counts['unaligned_sumset_reference']:
            dependencies.append('unaligned_sumset')
        if m.get('pin_digits', 0):
            dependencies.append('decimal_tail_coset')
        if m.get('pin2', False):
            dependencies.append('mod8_parity')
    if counts['exact_size_leaf']:
        dependencies.append('exact_size')
    return {'dependencies': dependencies, 'reference_counts': dict(counts), 'prime_ids': sorted(prime_ids),
            'format': m['format'], 'legacy_format': False, 'legacy_checker_applicable': False,
            'legacy_checker_reason': 'nd-sym multiset format is not accepted by v14_checknd_hd.py',
            'meta': m}


def audit():
    global ORDERS
    ORDERS = {p: d for p, d, a, w in read(HD / 'supply_B.json')}
    ledger = read(HERE / 'standalone_checks.json') if (HERE / 'standalone_checks.json').exists() else {'files': {}}
    available = collections.defaultdict(list)
    evidence, kills = {}, {}
    for file, check in ledger['files'].items():
        if check['result'] != 'PASS':
            continue
        assert sha(file) == check['sha256']
        stat = usage(file)
        stat['sha256'] = check['sha256']
        kills[file] = stat
        m = stat['meta']
        if m['scope'] != 'full':
            continue
        cs = tuple(c for c, n in m['groups'] for _ in range(n))
        available[(m['K'], cs)].append((m['qmin'], file))
        evidence[file] = (m, check['check'])
    cfg = read(HERE / 'assignment.json')['configurations']
    result = {}
    bytarget = collections.defaultdict(dict)
    bound = 2
    for name, rec in cfg.items():
        try:
            c = cover(9 * rec['S_low'] - 1, rec['far'], available)
            c.update(status='CLOSED', target=rec['target'], key=rec['key'], dim=len(rec['far']) + 1)
            # All assignments to distinct coefficient groups are independent axes.
            # Record the number of distinct far-digit words covered, without
            # identifying different coefficients under the symmetry quotient.
            c['distinct_coefficient_orderings'] = math.factorial(len(rec['far'])) // math.prod(math.factorial(v) for v in collections.Counter(rec['far']).values())
            c['kill_dependencies'] = sorted({d for file in c['domains'] for d in kills[file]['dependencies']})
            bound = max(bound, c['finite_Lmax'])
            bytarget[rec['target']][rec['key']] = rec
            result[name] = c
        except AssertionError as e:
            result[name] = {'status': 'BUDGET', 'target': rec['target'], 'key': rec['key'], 'dim': len(rec['far']) + 1, 'reason': str(e)}
    finite = finite_scan(bound, bytarget)
    members = set()
    for name, c in result.items():
        if c['status'] != 'CLOSED':
            continue
        actual = {v['member'] for v in finite['members'] if v['target'] == c['target'] and v['key'] == c['key']}
        for file in c['domains']:
            m, check = evidence[file]
            cs = tuple(co for co, n in m['groups'] for _ in range(n))
            for pt in check['solutions']:
                X = 10**pt[0] + m['K'] + sum(co * 10**q for co, q in zip(cs, pt[1:]))
                assert X % 9 == 0
                n = X // 9
                ds = str(n)
                S = sum((int(d) - 1) * 10**i for i, d in enumerate(ds[::-1][:3]))
                far = sorted(9 * (int(d) - 1) for d in ds[::-1][3:] if d != '1')
                key = str(S) + '|' + ','.join(map(str, far))
                if math.prod(map(int, ds)) == c['target'] and key == c['key']:
                    actual.add(n)
        c['members'] = sorted(actual)
        members.update((c['target'], c['key'], n) for n in actual)
    counts = {}
    for target in (32, 14112):
        counts[str(target)] = {}
        for dim in sorted({r['dim'] for r in result.values() if r['target'] == target}):
            rows = [r for r in result.values() if r['target'] == target and r['dim'] == dim]
            counts[str(target)][str(dim)] = {'assigned': len(rows), 'closed': sum(r['status'] == 'CLOSED' for r in rows), 'open': sum(r['status'] != 'CLOSED' for r in rows)}
    dependencies = collections.Counter(d for v in kills.values() for d in v['dependencies'])
    refs = collections.Counter()
    for v in kills.values():
        refs.update(v['reference_counts'])
    out = {'label': 'COMPUTED', 'counts_by_target_dimension': counts,
           'closed': sorted(k for k, v in result.items() if v['status'] == 'CLOSED'),
           'open': sorted(k for k, v in result.items() if v['status'] != 'CLOSED'),
           'configurations': result, 'finite_exception_scan': finite,
           'members': sorted(members), 'checker_counts': dict(collections.Counter(v['result'] for v in ledger['files'].values())),
           'certificate_dependency_counts': dict(dependencies), 'certificate_reference_counts': dict(refs),
           'auditor_files': {str(p.relative_to(ROOT)): sha(p) for p in sorted((HD / 'indep4').rglob('*')) if p.is_file()}}
    save(HERE / 'kill_usage.json', kills)
    save(HERE / 'summary.json', out)
    print(json.dumps({k: out[k] for k in ('counts_by_target_dimension', 'checker_counts', 'certificate_dependency_counts', 'certificate_reference_counts')}))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode', choices=('reconcile', 'search', 'check', 'audit'))
    ap.add_argument('--workers', type=int, default=12)
    ap.add_argument('--seconds', type=float, default=8)
    ap.add_argument('--lifts', type=int, default=100000000)
    ap.add_argument('--stage', default='broad8')
    ap.add_argument('--schedule', default='2,3,7,3,2,2,2,3')
    ap.add_argument('--mindim', type=int, default=1)
    ap.add_argument('--maxdim', type=int, default=9)
    ap.add_argument('--extra-floor', type=int, default=0)
    ap.add_argument('--pin-digits', type=int, default=3)
    ap.add_argument('--key')
    a = ap.parse_args()
    assert 1 <= a.workers <= 12 and a.seconds < 1200
    if a.mode == 'reconcile': reconcile()
    elif a.mode == 'search': search(a)
    elif a.mode == 'check': checks(a)
    else: audit()


if __name__ == '__main__':
    main()
