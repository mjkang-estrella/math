"""[F5] Run check_sym_F5.py on all certificates listed in
verification/highdim/sym5/deep_pin_certs.txt.  Stdlib only.
Run:  bash -c 'ulimit -v 6000000; python3 -I run_F5_deep.py [workers] [limit]'
Writes results to indep5/deep_pin_results.json and prints a summary.
"""
import sys, os, json, time, subprocess
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
VERIF = os.path.dirname(HERE)
LIST = os.path.join(VERIF, 'highdim', 'sym5', 'deep_pin_certs.txt')
F5 = os.path.join(HERE, 'check_sym_F5.py')

def run_one(path, timeout=1800):
    cmd = ['bash', '-c', 'ulimit -v 6000000; python3 -I "%s" "%s" 11 --json' % (F5, path)]
    t = time.time()
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        res = json.loads(out.stdout.strip().splitlines()[-1])
        res['wall'] = round(time.time() - t, 1)
        return res
    except subprocess.TimeoutExpired:
        return dict(result='TIMEOUT', problems=['timeout %ds' % timeout], wall=timeout)
    except Exception as e:
        return dict(result='ERROR', problems=['%s: %s' % (type(e).__name__, e)], wall=round(time.time() - t, 1))

def main():
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else None
    paths = [l.strip() for l in open(LIST) if l.strip()]
    if limit: paths = paths[:limit]
    print('certificates:', len(paths), 'workers:', workers, flush=True)
    results = {}
    done = 0
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for p, res in zip(paths, ex.map(run_one, paths)):
            results[p] = res
            done += 1
            if done % 250 == 0:
                npass = sum(1 for r in results.values() if r['result'] == 'PASS')
                print('  %d/%d done, %d PASS so far' % (done, len(paths), npass), flush=True)
    with open(os.path.join(HERE, 'deep_pin_results.json'), 'w') as f:
        json.dump(results, f)
    by = {}
    for p, r in results.items():
        stage = p.split('/certs/')[1].split('/')[0] if '/certs/' in p else '?'
        by.setdefault((stage, r['result']), 0)
        by[(stage, r['result'])] += 1
    print('\nverdicts by stage:')
    for k in sorted(by): print('  %-12s %s: %d' % (k[0], k[1], by[k]))
    npass = sum(1 for r in results.values() if r['result'] == 'PASS')
    print('TOTAL: %d/%d PASS' % (npass, len(results)))
    for p, r in results.items():
        if r['result'] != 'PASS':
            print('NOT PASS:', p, r['result'], r.get('problems', [])[:3])
    slow = sorted(results.items(), key=lambda kv: -kv[1].get('wall', 0))[:5]
    print('slowest:', [(os.path.basename(p), r.get('wall')) for p, r in slow])

if __name__ == '__main__':
    main()
