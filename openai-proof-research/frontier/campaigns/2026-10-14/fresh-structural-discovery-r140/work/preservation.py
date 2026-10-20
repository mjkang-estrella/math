# Original code, MIT. Read-only comparison of narrowly bound originals.
from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parents[1];P=R.parents[3]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
old=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r139'
expected=json.loads((R/'packet/private/context/r139-initial-inventory.json').read_text())['entries']
actual=[]
for f in sorted(old.rglob('*')):
    if f.is_symlink():raise ValueError('r139 symlink')
    actual.append(dict(path=str(f.relative_to(old)),kind='directory' if f.is_dir() else 'file',**({} if f.is_dir() else dict(size=f.stat().st_size,sha256=h(f)))))
rows=[]
for file in ['packet/private/context/bindings.json','packet/private/history/bindings.json']:
    for b in json.loads((R/file).read_text()):
        now=h(P/b['path'])
        rows.append(dict(path=b['path'],bound_sha256=b['sha256'],current_sha256=now,unchanged=now==b['sha256'],mutable_observation=b.get('mutable_observation',b['path'].startswith('frontier/findings/'))))
print(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),r139_entries=len(actual),r139_files=sum(x['kind']=='file' for x in actual),r139_current_root_unchanged=actual==expected,named_originals=rows,limits='Only named bindings and actual r139 root at observation times; no historical whole-parent or syscall claim.'),indent=2))
