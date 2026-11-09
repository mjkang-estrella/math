"""[F5] Regression: F5 vs the unmodified check_sym_F on 50 existing certificates.

Run:  bash -c 'ulimit -v 6000000; python3 -I regress_F5.py [nsample] [seed]'
Both checkers are executed as isolated subprocesses:
  bash -c 'ulimit -v 6000000; python3 -I <checker> <cert> 11 --json'
and the full JSON verdicts are compared (result, problems, claimed, brute, stats).
"""
import sys, os, json, random, subprocess, hashlib, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)                    # .../verification
sys.dont_write_bytecode = True

def v2(n):
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k

def meta_of(path):
    try:
        with open(path) as f:
            m = json.loads(f.readline())
        if m.get('k') != 'meta': return None
        return m
    except Exception:
        return None

def collect():
    dirs = [os.path.join(REPO, 'highdim', 'sym2', 'certs'),
            os.path.join(REPO, 'highdim', 'sym4', 'certs')]
    files = []
    for d in dirs:
        for root, _, names in os.walk(d):
            for nm in names:
                if nm.endswith('.jsonl'):
                    files.append(os.path.join(root, nm))
    return files

def run_one(checker, path, timeout=1200):
    cmd = ['bash', '-c', 'ulimit -v 6000000; python3 -I "%s" "%s" 11 --json' % (checker, path)]
    t = time.time()
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        res = json.loads(out.stdout.strip().splitlines()[-1])
        res['wall'] = round(time.time() - t, 1)
        return res
    except Exception as e:
        return dict(result='ERROR', problems=['%s: %s' % (type(e).__name__, e)], wall=round(time.time() - t, 1))

def pick(files, n, seed):
    rnd = random.Random(seed)
    # stratify by (source tree, t0==0 vs >0, dim<=5 vs >=6)
    buckets = {}
    pool = rnd.sample(files, min(len(files), 6000))
    for f in pool:
        m = meta_of(f)
        if not m or m.get('scope') != 'full' or m.get('domain') != 'unordered': continue
        K = m['K']; t0 = v2(K); dim = m['dim']; k = int(m.get('pin_digits') or 0)
        tree = 'sym2' if os.sep + 'sym2' + os.sep in f else 'sym4'
        b = (tree, t0 == 0, dim <= 5, k > 0)
        buckets.setdefault(b, []).append((f, t0, dim, k))
    keys = sorted(buckets)
    print('strata:', {str(k): len(v) for k, v in zip(keys, [buckets[k] for k in keys])})
    chosen = []
    # round-robin over strata, preferring variety in t0
    for key in keys:
        lst = buckets[key][:]
        rnd.shuffle(lst)
        chosen.extend(lst[:max(1, n // (2 * len(keys)))])
    # fill up randomly
    rest = [x for k in keys for x in buckets[k] if x not in chosen]
    rnd.shuffle(rest)
    while len(chosen) < n and rest:
        chosen.append(rest.pop())
    return chosen[:n]

def main():
    nsample = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    base = os.path.join(HERE, 'check_sym_F_base.py')
    f5 = os.path.join(HERE, 'check_sym_F5.py')
    # integrity: base copy is byte-identical to the original indep4 checker
    orig = os.path.join(REPO, 'indep4', 'check_sym_F.py')
    h = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
    assert h(base) == h(orig), 'check_sym_F_base.py is not a verbatim copy of indep4/check_sym_F.py'
    print('base copy verified byte-identical to indep4/check_sym_F.py')

    files = collect()
    print('certificate files found:', len(files))
    sample = pick(files, nsample, seed)
    print('sampled', len(sample), 'certificates')
    for i, (f, t0, dim, k) in enumerate(sample):
        print('  %2d t0=%-3d dim=%d k=%d %s' % (i, t0, dim, k, os.path.relpath(f, REPO)))

    jobs = [(f, ) for f, *_ in sample]
    with ThreadPoolExecutor(max_workers=4) as ex:
        futs = {ex.submit(run_one, base, j[0]): ('base', j[0]) for j in jobs}
        futs.update({ex.submit(run_one, f5, j[0]): ('f5', j[0]) for j in jobs})
        results = {}
        for fut in futs:
            tag, path = futs[fut]
            results[(tag, path)] = fut.result()
    bad = 0
    for f, t0, dim, k in sample:
        rb = results[('base', f)]; rf = results[('f5', f)]
        same = (rb['result'] == rf['result'] and rb.get('problems') == rf.get('problems')
                and rb.get('claimed') == rf.get('claimed') and rb.get('brute') == rf.get('brute')
                and rb.get('stats') == rf.get('stats'))
        if not same:
            bad += 1
            print('MISMATCH', f)
            print('  base:', rb['result'], rb.get('problems'), rb.get('stats'))
            print('  f5  :', rf['result'], rf.get('problems'), rf.get('stats'))
        else:
            print('  %-4s t0=%-3d k=%-2d wall %5.1f/%5.1f  %s' % (
                rf['result'], t0, k, rb.get('wall', -1), rf.get('wall', -1), os.path.basename(f)))
    print('\n%d/%d identical verdicts' % (len(sample) - bad, len(sample)))
    print('f5 PASS count:', sum(1 for f, *_ in sample if results[('f5', f)]['result'] == 'PASS'))
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
