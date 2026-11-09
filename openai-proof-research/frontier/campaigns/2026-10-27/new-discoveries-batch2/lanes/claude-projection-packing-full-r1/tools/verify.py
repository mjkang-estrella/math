"""Separate final verification. Writes ONLY verification-receipt.json (excluded from the manifest).
Checks: (1) scientific originals and lane copies against scientific-freeze.json; (2) administrative
snapshots against their snapshot hashes (live mutable files are NOT compared); (3) every manifest
entry; (4) no unlisted lane file besides the two explicit exclusions; (5) tmp/ empty;
(6) exact replay of exp5 (Theorem A' on the source V) matches the recorded output."""
import datetime, hashlib, json, os, subprocess, sys
L = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
B = os.path.normpath(os.path.join(L, '..', '..'))
h = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
res = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'checks': {}}
fz = json.load(open(os.path.join(L, 'scientific-freeze.json')))
sci = []
for e in fz['scientific']:
    o = os.path.join(B, e['original'].split('new-discoveries-batch2/', 1)[1])
    sci.append(h(o) == e['sha256'] and h(os.path.join(L, e['copy'])) == e['sha256'])
res['checks']['scientific_originals_and_copies'] = all(sci) and len(sci) == 11
res['checks']['admin_snapshots_unchanged'] = all(h(os.path.join(L, e['copy'])) == e['sha256_at_snapshot'] for e in fz['administrative_snapshot_only'])
man = json.load(open(os.path.join(L, 'manifest.json')))
res['checks']['manifest_entries'] = all(h(os.path.join(L, f['path'])) == f['sha256'] for f in man['files'])
listed = {f['path'] for f in man['files']} | set(man['excluded_explicitly'])
actual = set()
for root, dirs, names in os.walk(L):
    dirs[:] = [d for d in dirs if d not in ('tmp', '__pycache__')]
    actual |= {os.path.relpath(os.path.join(root, n), L) for n in names}
res['checks']['no_unlisted_files'] = (actual - listed) <= {'verification-receipt.json'} and not (actual - listed - {'verification-receipt.json'})
res['unlisted'] = sorted(actual - listed - {'verification-receipt.json'})
tmp = os.path.join(L, 'tmp')
res['checks']['tmp_empty'] = (not os.path.isdir(tmp)) or os.listdir(tmp) == []
src = os.path.join(L, 'sources', 'bourgain1982')
res['checks']['bourgain_original_equals_frozen'] = h(os.path.join(src, 'bourgain.pdf')) == h(os.path.join(src, 'bourgain.frozen.pdf')) == '0c097b3e572854a076f9643593106772e6a550297048dd65016b24bf7b622009'
out = subprocess.run([sys.executable, '-I', os.path.join(L, 'tools', 'exp5_geofrac_w.py')], capture_output=True, text=True).stdout
res['checks']['exp5_exact_replay_matches'] = json.loads(out) == json.load(open(os.path.join(L, 'runs', 'exp5.json')))
res['manifest_sha256'] = h(os.path.join(L, 'manifest.json'))
res['all_pass'] = all(res['checks'].values())
json.dump(res, open(os.path.join(L, 'verification-receipt.json'), 'w'), indent=1)
print(json.dumps(res, indent=1))
sys.exit(0 if res['all_pass'] else 1)
