"""Final verifier for r354. Exit nonzero on any mismatch.
1) manifest.json: exact sha256+size for every lane file except manifest.json and verification-receipt.json,
   and no unlisted files; 2) input-freeze.json: in-place source originals unchanged;
3) re-run the asserting exact checks and compare stdout with the recorded runs."""
import hashlib, json, os, subprocess, sys
LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LANES = os.path.dirname(LANE)
EXCL = {'manifest.json', 'verification-receipt.json'}
def h(p):
    b = open(p, 'rb').read(); return hashlib.sha256(b).hexdigest(), len(b)
bad = []
man = json.load(open(os.path.join(LANE, 'manifest.json')))
listed = {f['path'] for f in man['files']}
for f in man['files']:
    p = os.path.join(LANE, f['path'])
    if not os.path.isfile(p): bad.append('missing ' + f['path']); continue
    if h(p) != (f['sha256'], f['size']): bad.append('hash ' + f['path'])
actual = set()
for r, ds, fs in os.walk(LANE):
    for x in fs:
        rel = os.path.relpath(os.path.join(r, x), LANE)
        if rel not in EXCL: actual.add(rel)
for x in sorted(actual - listed): bad.append('unlisted ' + x)
fz = json.load(open(os.path.join(LANE, 'input-freeze.json')))
for f in fz['files']:
    p = os.path.join(LANES, f['path'])
    if not os.path.isfile(p) or h(p) != (f['sha256'], f['size']): bad.append('input changed ' + f['path'])
env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1')
for s in ['check_t1_t2_counterexamples', 'check_degree4_generation']:
    r = subprocess.run([sys.executable, '-B', os.path.join(LANE, 'checks', s + '.py')], capture_output=True, text=True, env=env)
    if r.returncode != 0: bad.append('check failed ' + s)
    if r.stdout != open(os.path.join(LANE, 'runs', s + '.stdout')).read(): bad.append('stdout differs ' + s)
print(json.dumps({'status': 'FAIL' if bad else 'PASS', 'manifest_files': len(listed), 'inputs_verified': len(fz['files']), 'problems': bad}, indent=1))
sys.exit(1 if bad else 0)
