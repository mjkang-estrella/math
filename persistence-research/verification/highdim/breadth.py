"""Budgeted, resumable breadth pass. Enumeration is E/E2's, never the solve labels.

All new certificates use the existing driver semantics: unordered at k>=3,
every distinct ordering otherwise. No incomplete tree is written as a certificate.
Usage: breadth.py TARGET [workers=12] [seconds/config=30] [nodes/attempt=100000]
                  [lifts/config=5000000] [optional max far count]
"""
import sys
sys.dont_write_bytecode = True
import os, json, time, signal, itertools, multiprocessing as mp, traceback
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from inventory import configurations
import run_target, gen_hd
from hnt import vp

HERE = os.path.dirname(os.path.abspath(__file__))
SUP = run_target.SUP

class Budget(Exception):
    pass

class BudgetGen(gen_hd.Gen):
    def expand(self, r, M, f):
        cost = f ** self.dim
        if self.account['lifts'] + cost > self.account['max_lifts']:
            raise Budget('lift cap')
        self.account['lifts'] += cost
        return super().expand(r, M, f)

def atomic_json(path, obj):
    tmp = path + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(obj, f, indent=1)
    os.replace(tmp, path)

def jobs_for(t, S, far):
    outdir = os.path.join(HERE, 'certs', f't{t}')
    os.makedirs(outdir, exist_ok=True)
    jobs = []
    for K, free in run_target.slices(9*S-1, far):
        qmin = max(3, vp(K, 2)+1) if free else vp(K, 2)+1
        ordered = len(free) <= 2
        for coefs in (run_target.orderings(free) if ordered else [free]):
            suffix = ('o' if ordered else 'u') + ('_'.join(map(str, coefs)) or 'none')
            fn = os.path.join(outdir, f'c_S{S}_K{K}_{suffix}.jsonl')
            jobs.append((K, tuple(coefs), qmin, ordered, fn))
    return sorted(jobs, key=lambda j: (-len(j[1]), j[0], j[1]))

def existing_cert(job):
    K, coefs, qmin, ordered, fn = job
    if not os.path.exists(fn): return None
    with open(fn) as f:
        meta = json.loads(next(f)); n = 0; sols = []
        assert (meta['K'], tuple(meta['coefs']), meta['qmin'], meta['domain']) == (
            K, coefs, qmin, 'ordered' if ordered else 'unordered')
        for line in f:
            r = json.loads(line); n += 1
            if r['k'] == 'l' and 'sz' in r['x']:
                sols += r['x']['sol']
    return n, sols

def work(arg):
    t, S, far, detail, seconds, nodes, lifts_cap = arg
    start = time.monotonic()
    key = f"{S}|{','.join(map(str, far))}"
    logdir = os.path.join(HERE, 'logs', f'breadth_t{t}')
    os.makedirs(logdir, exist_ok=True)
    logfn = os.path.join(logdir, key.replace('|', '_').replace(',', '_') + '.log')
    log = open(logfn, 'w', buffering=1)
    olderr = sys.stderr; sys.stderr = log
    account = {'lifts': 0, 'max_lifts': lifts_cap}
    records = []; sols = []; stop = None
    jobs = jobs_for(t, S, far)
    def timeout(signum, frame): raise Budget('wall time')
    old_handler = signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        for job in jobs:
            K, coefs, qmin, ordered, fn = job
            rec = {'K': K, 'coefs': list(coefs), 'qmin': qmin,
                   'domain': 'ordered' if ordered else 'unordered',
                   'file': os.path.relpath(fn, HERE)}
            cached = existing_cert(job)
            if cached:
                count, ss = cached
                rec.update(status='closed', info={'nodes': count, 'cached': True})
                records.append(rec)
                sols += [[K, list(coefs), s] for s in ss]
                continue
            last = None
            schedules = run_target.SCHED.get(len(coefs)+1, run_target.SCHED[5])
            if t not in (16, 24, 32, 112):
                # The resumed probe reduces a dim-4 example from 6.3M lifts
                # and 50k nodes to 0.40M lifts and 4k nodes by aligning 7 early.
                schedules = ([[2,3,7,3,2,2,2,3,5]] if len(coefs) >= 3 else schedules[:1])
            for sched in schedules:
                try:
                    G = BudgetGen(coefs, K, qmin, SUP, ordered, maxp=10**12)
                    G.account = account
                    ns, info, status = gen_hd.run(
                        G, sched, workers=1, cap_level=nodes, max_nodes=nodes,
                        budget_s=max(.01, seconds-(time.monotonic()-start)))
                    last = {'schedule': sched, 'reason': status, 'frontiers': info}
                except gen_hd.NodeBudgetExceeded as ex:
                    ns = None; last = {'schedule': sched, 'reason': str(ex)}
                if ns is not None:
                    # Disarm while atomically writing a complete tree. Re-arm the
                    # remaining configuration budget before moving to another slice.
                    signal.setitimer(signal.ITIMER_REAL, 0)
                    gen_hd.write_cert(fn+'.tmp', G, ns, {'sched': sched, 'maxp': 10**12})
                    os.replace(fn+'.tmp', fn)
                    rec.update(status='closed', info={'nodes': len(ns), 'schedule': sched})
                    records.append(rec)
                    sols += [[K, list(coefs), list(s)] for s in gen_hd.solutions(ns)]
                    if time.monotonic()-start >= seconds: raise Budget('wall time after write')
                    signal.setitimer(signal.ITIMER_REAL, seconds-(time.monotonic()-start))
                    break
            else:
                rec.update(status='BUDGET', info=last)
                records.append(rec)
                # Every configuration gets an attempt before spending more on a
                # configuration already known to need a larger budget.
                stop = last['reason']; break
    except (Budget, gen_hd.NodeBudgetExceeded, MemoryError, RecursionError) as ex:
        stop = f'{type(ex).__name__}: {ex}'
    except Exception:
        stop = 'ERROR'; traceback.print_exc(file=log)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)
        sys.stderr = olderr; log.close()
    done = {r['file'] for r in records}
    pending = len(jobs)-len(done)
    closed = not pending and all(r['status'] == 'closed' for r in records)
    result = {'multiset': list(detail['multiset']), 'S_low': S, 'far': list(far),
              'status': 'CLOSED' if closed else ('ERROR' if stop == 'ERROR' else 'BUDGET'),
              'slices': len(run_target.slices(9*S-1, far)), 'certs': len(jobs),
              'jobs': records, 'pending_jobs': pending, 'sz_solutions': sorted(sols),
              'budget': {'seconds': seconds, 'nodes_per_attempt': nodes, 'lifts_per_config': lifts_cap},
              'elapsed_s': round(time.monotonic()-start, 3), 'lifts_attempted': account['lifts'],
              'stop_reason': stop}
    return key, result

def main():
    t = int(sys.argv[1]); workers = int(sys.argv[2]) if len(sys.argv)>2 else 12
    seconds = float(sys.argv[3]) if len(sys.argv)>3 else 30
    nodes = int(sys.argv[4]) if len(sys.argv)>4 else 100000
    cap = int(sys.argv[5]) if len(sys.argv)>5 else 5000000
    maxfar = int(sys.argv[6]) if len(sys.argv)>6 else 99
    assert 1 <= workers <= 24
    cfg = configurations(t)
    resfn = os.path.join(HERE, f'results_t{t}.json')
    results = json.load(open(resfn)) if os.path.exists(resfn) else {}
    authoritative = {f"{S}|{','.join(map(str, f))}" for S, f, _ in cfg}
    assert set(results) <= authoritative, 'extra configuration in incoming results'
    todo = [(t, S, f, d, seconds, nodes, cap) for S, f, d in cfg
            if len(f) <= maxfar and results.get(f"{S}|{','.join(map(str, f))}", {}).get('status') != 'CLOSED']
    # Smallest dimensions first; higher-dimensional attempts remain mandatory.
    todo.sort(key=lambda a: (len(a[2]), a[1], a[2]))
    print(f't={t}: authoritative={len(cfg)} todo={len(todo)} workers={workers}', flush=True)
    with mp.get_context('fork').Pool(workers, maxtasksperchild=1) as pool:
        for i, (key, result) in enumerate(pool.imap_unordered(work, todo, chunksize=1), 1):
            results[key] = result; atomic_json(resfn, results)
            print(f'{i}/{len(todo)} {key} {result["status"]} '
                  f'{sum(r["status"]=="closed" for r in result["jobs"])}/{result["certs"]} '
                  f'{result["elapsed_s"]}s {result["stop_reason"]}', flush=True)
    if maxfar == 99: assert set(results) == authoritative
    print('SUMMARY', {s: sum(r['status']==s for r in results.values())
                      for s in sorted({r['status'] for r in results.values()})}, flush=True)

if __name__ == '__main__': main()
