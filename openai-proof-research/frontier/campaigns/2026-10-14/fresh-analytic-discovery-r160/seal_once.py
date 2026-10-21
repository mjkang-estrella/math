"""One-shot own-payload seal. All paths stay under the exclusive r160 root."""
from pathlib import Path
import hashlib,json
ROOT=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r160')
EXCLUDE={'FINAL.md','REPORT.md','MANIFEST.json'}
if (ROOT/'MANIFEST.json').exists():raise SystemExit('Already sealed; refusing to reseal')
entries=[]
for p in sorted(ROOT.rglob('*')):
    if p.is_symlink():raise SystemExit('symlink')
    if p.is_file():
        if p.stat().st_nlink!=1:raise SystemExit('unexpected hard link')
        name=p.relative_to(ROOT).as_posix()
        if name not in EXCLUDE:
            b=p.read_bytes();entries.append({'path':name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    elif not p.is_dir():raise SystemExit('special node')
m={'schema':'r160.exact-files.v1','excluded_root_envelopes':sorted(EXCLUDE),'files':entries}
(ROOT/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'files':len(entries),'bytes':sum(x['bytes'] for x in entries)}))
for name in ['FINAL.md','MANIFEST.json','REPORT.md']:
    print(name,hashlib.sha256((ROOT/name).read_bytes()).hexdigest())
