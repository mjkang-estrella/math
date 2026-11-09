"""Separate verification after final writes.  Checks:
 (1) every manifest entry rehashes identically; no unlisted lane files except
     the two explicit exclusions;
 (2) external originals unchanged, and equal to pre-run hashes and frozen copies;
 (3) exact checks rerun (subprocess) give byte-identical output to runs/exact_checks.out.
Writes verification-receipt.json (itself excluded from the manifest)."""
import os, sys, json, hashlib, subprocess, datetime

lane = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
B = os.path.normpath(os.path.join(lane, '..', '..'))


def h(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


m = json.load(open(os.path.join(lane, 'manifest.json')))
res = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'checks': {}}
bad = [f for f, x in m['files'].items() if not os.path.exists(os.path.join(lane, f)) or h(os.path.join(lane, f)) != x]
present = set()
for root, dirs, fs in os.walk(lane):
    dirs[:] = [d for d in dirs if d != '__pycache__']
    for f in fs:
        present.add(os.path.relpath(os.path.join(root, f), lane))
unlisted = sorted(present - set(m['files']) - set(m['excluded_explicitly']))
res['checks']['manifest_rehash'] = {'entries': len(m['files']), 'mismatches': bad, 'unlisted': unlisted,
                                    'excluded_explicitly': m['excluded_explicitly']}
ext_bad = [r for r, x in m['external_originals'].items() if h(os.path.join(B, r)) != x]
pre = {}
for line in open(os.path.join(lane, 'work', 'pre-hashes.txt')):
    a, p = line.split(None, 1)
    pre[os.path.normpath(p.strip())] = a
# scientific originals must be unchanged; live administrative files (ledger,
# NEXT, prior-context, AGENTS) are root-mutable: drift is recorded, not fatal
# (attempt 1 wrongly failed on root's NEXT.md edits; preserved in runs/).
ADMIN = ('ledger.json', 'NEXT.md', 'prior-campaign-context.json', 'AGENTS.md')
sci = {p: a for p, a in pre.items() if not p.endswith(ADMIN)}
adm = {p: a for p, a in pre.items() if p.endswith(ADMIN)}
pre_bad = [p for p, a in sci.items() if h(p) != a]
res['checks']['administrative_drift_not_bound'] = [os.path.basename(p) for p, a in adm.items() if h(p) != a]
pairs = [('frozen/even.pdf', 'lanes/sol-fresh-source-discovery-r213/frozen/even.pdf'),
         ('frozen/even-abs.html', 'lanes/sol-fresh-source-discovery-r213/frozen/even-abs.html')]
copy_bad = [a for a, b in pairs if h(os.path.join(lane, a)) != h(os.path.join(B, b))]
res['checks']['originals'] = {'external_mismatches': ext_bad, 'prehash_mismatches': pre_bad,
                              'copy_vs_original_mismatches': copy_bad, 'scientific_prehash_entries': len(sci)}
out = subprocess.run([sys.executable, '-B', os.path.join(lane, 'work', 'exact_checks.py')],
                     capture_output=True, timeout=200).stdout
ref = open(os.path.join(lane, 'runs', 'exact_checks.out'), 'rb').read()
res['checks']['exact_checks_replay'] = {'identical': out == ref, 'sha256': hashlib.sha256(out).hexdigest()}
ok = not bad and not unlisted and not ext_bad and not pre_bad and not copy_bad and out == ref
res['PASS'] = ok
res['manifest_sha256'] = h(os.path.join(lane, 'manifest.json'))
json.dump(res, open(os.path.join(lane, 'verification-receipt.json'), 'w'), indent=1)
print(json.dumps(res))
sys.exit(0 if ok else 1)
