# run check_sym_F on a list of certificates in parallel.  python3 -I sym2/run_py.py list.json outdir [workers]
import subprocess, json, sys, os, time
from concurrent.futures import ThreadPoolExecutor
lst = json.load(open(sys.argv[1])); out = sys.argv[2]; W = int(sys.argv[3]) if len(sys.argv) > 3 else 14
os.makedirs(out, exist_ok=True)
files = sorted(lst if isinstance(lst, list) else lst.keys())
def run(f):
    name = f.split('/certs/')[-1].replace('/', '__')
    dst = os.path.join(out, name + '.json')
    if os.path.exists(dst) and os.path.getsize(dst) > 0: return
    m = json.loads(open(f).readline())
    F = sum(g[1] for g in m['groups']); br = min(m['qmin'] + F + 1, 40)
    t = time.time()
    try:
        r = subprocess.run(['bash', '-c', "ulimit -v 8000000; timeout 1500 python3 -I check_sym_F.py %s %d --json" % (f, br)], capture_output=True, text=True, timeout=1600)
        line = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else json.dumps(dict(file=f, result='NOOUTPUT', problems=[r.stderr[-300:]]))
    except subprocess.TimeoutExpired:
        line = json.dumps(dict(file=f, result='TIMEOUT', problems=['timeout']))
    d = json.loads(line); d['seconds'] = round(time.time() - t, 1); d['file'] = f
    open(dst, 'w').write(json.dumps(d))
with ThreadPoolExecutor(W) as ex: list(ex.map(run, files))
print('done', len(files))
