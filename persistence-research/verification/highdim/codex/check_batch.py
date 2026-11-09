"""Run both requested checkers, retain per-file hashes, logs, exits, and timings.
Usage: check_batch.py [workers=12] [target|'all'=all] [timeout/check=1200]
The small brute box is supplementary: the complete residue-tree checks are not capped.
"""
import sys
sys.dont_write_bytecode = True
import os, json, glob, hashlib, time, subprocess, shlex, concurrent.futures
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, HERE)
from breadth import atomic_json

def sha256(fn):
    h = hashlib.sha256()
    with open(fn, 'rb') as f:
        for block in iter(lambda: f.read(1<<20), b''): h.update(block)
    return h.hexdigest()

def check(arg):
    name, checker, fn, digest, timeout = arg
    rel = os.path.relpath(fn, HERE)
    logfn = os.path.join(HERE, 'logs', 'checks', name, rel.replace('/', '__')+'.log')
    os.makedirs(os.path.dirname(logfn), exist_ok=True)
    # Match the parent's usual independent box (L<=12); this includes all far
    # coefficient orderings and is additional to exact sz and full-tree checks.
    with open(fn) as f: meta = json.loads(next(f))
    brute = {1: 100, 2: 60, 3: 30}.get(meta['dim'], 12)
    args = ['python3', '-I', os.path.join(HERE, 'checker_entry.py'), checker, fn, str(brute)]
    if name == 'hd': args.append('1')
    command = 'ulimit -v 6000000; ' + shlex.join(args)
    start = time.monotonic()
    try:
        with open(logfn, 'w') as log:
            r = subprocess.run(['bash', '-c', command], stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
        out = open(logfn).read()
        status = 'PASS' if r.returncode == 0 and 'RESULT: PASS' in out else 'FAIL'
        rc = r.returncode
    except subprocess.TimeoutExpired:
        status = 'BUDGET'; rc = None
    return f'{name}|{rel}', {'checker': name, 'file': rel, 'sha256': digest, 'status': status,
                            'exit': rc, 'elapsed_s': round(time.monotonic()-start,3),
                            'brute_Lmax': brute, 'log': os.path.relpath(logfn, HERE)}

def main():
    workers = int(sys.argv[1]) if len(sys.argv)>1 else 12
    target = sys.argv[2] if len(sys.argv)>2 else 'all'
    timeout = float(sys.argv[3]) if len(sys.argv)>3 else 1200
    assert 1 <= workers <= 24
    files = sorted(glob.glob(os.path.join(HERE, 'certs', '**', '*.jsonl'), recursive=True)) if target=='all' else sorted(glob.glob(os.path.join(HERE, 'certs', 't'+target, '*.jsonl')))
    outfn = os.path.join(HERE, sys.argv[4] if len(sys.argv)>4 else 'checker_results.json')
    cachefn = outfn if os.path.exists(outfn) else os.path.join(HERE, 'checker_results.json')
    old = json.load(open(cachefn)) if os.path.exists(cachefn) else {}
    checkers = [('hd', os.path.join(HERE, 'checkhd.py'))]
    parent = os.path.join(ROOT, 'verification', 'v14_checknd_hd.py')
    if os.path.exists(parent): checkers.append(('v14', parent))
    jobs = []
    for fn in files:
        digest = sha256(fn)
        for name, checker in checkers:
            prev = old.get(name+'|'+os.path.relpath(fn,HERE), {})
            if prev.get('sha256') == digest and prev.get('status') == 'PASS': continue
            jobs.append((name, checker, fn, digest, timeout))
    # Check large certificates early, so the last few are short tasks.
    jobs.sort(key=lambda a: -os.path.getsize(a[2]))
    print(f'certificates={len(files)} checker jobs={len(jobs)} workers={workers}', flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(check, arg) for arg in jobs]
        for i, fut in enumerate(concurrent.futures.as_completed(futures), 1):
            key, result = fut.result(); old[key] = result; atomic_json(outfn, old)
            print(f'{i}/{len(jobs)} {key} {result["status"]} {result["elapsed_s"]}s', flush=True)
    print('SUMMARY', {name: {s: sum(r['checker']==name and r['status']==s for r in old.values())
                             for s in ('PASS','FAIL','BUDGET')} for name,_ in checkers}, flush=True)

if __name__ == '__main__': main()
