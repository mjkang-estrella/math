"""Hash-bind the frozen inputs of this lane (read-only).
   python3 -I -B scripts/hashbind.py OUT.json [COMPARE.json]
Directories are walked without following symlinks; symlinks are recorded by target."""
import hashlib, json, os, sys, datetime
NT = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31'
B2 = os.path.dirname(NT)
ROOTS = [
    NT + '/conference-mds-resume-r4', NT + '/fresh-corpus-r3/sources', NT + '/fresh-corpus-r3/literal-records.json',
    NT + '/conference-fidelity-review-r1', NT + '/conference-parent-revision-r1', NT + '/conference-significance-review-r1',
    NT + '/conference-significance-objections-r1.json', NT + '/conference-significance-adjudication-r2',
    NT + '/conference-adjudication-parent-integration-r2.json', NT + '/conference-primary-comparison-r3',
    NT + '/conference-primary-parent-integration-r3.json', NT + '/held-reopen-r1', NT + '/held-reopen-root-ruling-r1.json',
    NT + '/replay-fit-r1', NT + '/conference-parent-final-r1', NT + '/AGENTS.md', B2 + '/AGENTS.md',
    '/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md',
    B2 + '/lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0002.jsonl',
    NT + '/asep-manuscript-r1/tmp/pdfdeps', NT + '/asep-manuscript-r1/dossier/paper/build_paper.py',
    NT + '/conference-manuscript-r1/TASK.txt', NT + '/conference-manuscript-r1/launch.json',
]
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()
def walk(r):
    if os.path.islink(r):
        yield r, 'symlink:' + os.readlink(r); return
    if os.path.isfile(r):
        yield r, sha(r); return
    for d, ds, fs in os.walk(r, followlinks=False):
        ds.sort()
        for n in sorted(fs) + sorted(x for x in ds if os.path.islink(os.path.join(d, x))):
            p = os.path.join(d, n)
            yield p, ('symlink:' + os.readlink(p)) if os.path.islink(p) else sha(p)
out = {}
missing = [r for r in ROOTS if not os.path.lexists(r)]
for r in ROOTS:
    if os.path.lexists(r):
        for p, h in walk(r):
            out[p] = h
rec = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'roots': ROOTS, 'missing_roots': missing,
       'files': len(out), 'sha256': out}
if len(sys.argv) > 2:
    old = json.load(open(sys.argv[2]))['sha256']
    rec['compare_to'] = sys.argv[2]
    rec['changed'] = sorted(p for p in old if p in out and out[p] != old[p])
    rec['missing'] = sorted(p for p in old if p not in out)
    rec['added'] = sorted(p for p in out if p not in old)
    rec['identical'] = not (rec['changed'] or rec['missing'] or rec['added'])
json.dump(rec, open(sys.argv[1], 'w'), indent=1)
print(rec['files'], 'files; missing roots', missing, '; identical' if rec.get('identical') else '', rec.get('changed', ''), rec.get('missing', ''), rec.get('added', ''))
