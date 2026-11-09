import hashlib, json, os, subprocess, sys, datetime
# Separate final verification: manifest inventory/hashes, scientific original/copy bindings, reference hashes.
L = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/claude-richardson-prior-substantive-r2'
EXCLUDE = {'manifest.json', 'verification-receipt.json'}
h = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
m = json.load(open(L + '/manifest.json'))
listed = {e['path'] for e in m['files']}
actual = {os.path.relpath(os.path.join(r, n), L) for r, _, ns in os.walk(L) for n in ns} - EXCLUDE
hash_ok = all(h(os.path.join(L, e['path'])) == e['sha256'] for e in m['files'])
sub = {}
for script in ('bind.py', 'bind_supplement.py', 'bind_r216.py'):
    r = subprocess.run([sys.executable, '-I', L + '/' + script, 'verify'], capture_output=True, text=True)
    sub[script] = r.returncode == 0
res = {'verified_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'manifest_sha256': h(L + '/manifest.json'),
       'inventory_match': listed == actual, 'missing': sorted(actual - listed), 'extra': sorted(listed - actual),
       'hashes_ok': hash_ok, 'bindings_ok': sub, 'excluded': sorted(EXCLUDE)}
res['all_ok'] = res['inventory_match'] and hash_ok and all(sub.values())
json.dump(res, open(L + '/verification-receipt.json', 'w'), indent=1)
print(json.dumps(res)); sys.exit(0 if res['all_ok'] else 1)
