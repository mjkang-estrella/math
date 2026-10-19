from pathlib import Path
import json,hashlib,re,shutil
r=Path(__file__).resolve().parents[1];repo=r.parents[3];p=r/'packet'
def sha(b):return hashlib.sha256(b).hexdigest()
a=json.loads((p/'private/upstream/register.json').read_text())
for x in a:
 f=p/x['local'];family=x['local'].split('/')[2];name=f.name
 keep=family=='372' or (family=='328' and name=='00-introduction.tex') or (family=='330' and name=='reduction.tex') or (family=='086' and name in {'introduction.tex','outer.tex','completion.tex'})
 x['retained']=keep;x['read']='complete section before freeze' if keep else 'acquired only; unread body removed'
 if keep:x['labels']=re.findall(r'\\label\{([^}]+)\}',f.read_text())
 else:
  assert sha(f.read_bytes())==x['sha256'];f.unlink()
(p/'private/upstream/register.json').write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
for d in sorted((p/'private/upstream').rglob('*'),reverse=True):
 if d.is_dir() and not any(d.iterdir()):d.rmdir()
# Keep one full final inventory and the earlier receipts, with deletion receipts.
removed=[]
for f in (p/'private/search').rglob('*.json'):
 if f.name in {'hits.json','inventory.json'} and 'broad-prefreeze' not in f.parts:
  b=f.read_bytes();removed.append({'path':str(f.relative_to(p)),'bytes':len(b),'sha256':sha(b)});f.unlink()
(p/'private/search/removed.json').write_text(json.dumps(removed,indent=2)+'\n')
paths=[
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r125/REPORT.md',
 *['frontier/campaigns/2026-10-14/fresh-analytic-discovery-r125/packet/public/'+n for n in ['report.md','annular-sectors.md','renewal-feasibility.md','other-screens.md','reading-limits.md']],
 'frontier/campaigns/2026-10-14/discovery-analytic-r125-parent/intake.json',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r117/packet/public/fixed-points.md',
 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r97/checkpoint.md',
 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r98/330-technical-screen.md',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r35/report.md',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r116/packet/public/screens.md',
 'frontier/iterations/i331-bi-sobolev.md','frontier/experiments/i331_bi_sobolev/analysis.md',
 *['frontier/iterations/'+n for n in ['i112-inverse-boundary-discovery.md','i115-physical-elasticity-continuation.md','i118-physical-quotient-angular.md','i121-physical-transfer-bound.md']],
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r30/next-lead.md']
rows=[]
for i,s in enumerate(paths):
 b=(repo/s).read_bytes();dest=p/'private/history'/f'{i:02}-{Path(s).name}';dest.write_bytes(b);rows.append({'original':s,'local':str(dest.relative_to(p)),'sha256':sha(b),'bytes':len(b),'reading':'See public/reading-limits.md; copies do not assert full semantic reading'})
(p/'private/history/register.json').write_text(json.dumps(rows,indent=2)+'\n')
rows=[]
for n in range(23,41):
 f=next((repo/'frontier/findings').glob(f'R{n:03}-*'));dest=p/'private/context'/f.name;b=f.read_bytes();dest.write_bytes(b);rows.append({'original':str(f.relative_to(repo)),'local':str(dest.relative_to(p)),'sha256':sha(b),'reading':'scope statement only; not complete proof/gate'})
(p/'private/context/findings-register.json').write_text(json.dumps(rows,indent=2)+'\n')
print({'canonical_acquired':len(a),'retained':sum(x['retained'] for x in a),'removed_search_bodies':len(removed),'history_copies':len(paths)})
