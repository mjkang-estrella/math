"""Hash every regular file of the frozen read-only inputs used by this lane.
Usage: python3 -I tools/hash_frozen.py OUT.json"""
import hashlib, json, os, sys, pathlib, datetime
BASE = pathlib.Path(__file__).resolve().parents[2]
ROOTS = ['expanded-corpus-r49', 'paley-config-fidelity-review-r1',
         'paley-config-parent-integration-r1', 'paley-config-source-review-r2']
out = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'base': str(BASE), 'roots': ROOTS, 'files': {}}
for r in ROOTS:
    for dp, dn, fn in os.walk(BASE / r):
        dn.sort()
        for f in sorted(fn):
            p = pathlib.Path(dp) / f
            if p.is_symlink() or not p.is_file():
                continue
            h = hashlib.sha256()
            with p.open('rb') as fh:
                for b in iter(lambda: fh.read(1 << 20), b''):
                    h.update(b)
            out['files'][str(p.relative_to(BASE))] = h.hexdigest()
agg = hashlib.sha256(''.join(k + ' ' + v + '\n' for k, v in sorted(out['files'].items())).encode()).hexdigest()
out['count'] = len(out['files']); out['aggregate_sha256'] = agg
pathlib.Path(sys.argv[1]).write_text(json.dumps(out, indent=1))
print(out['count'], agg)
