"""Late named-original capture, not first-read preservation. Writes only in r108."""
from pathlib import Path
import fnmatch,hashlib,json,datetime
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT.parents[3]
patterns=['*analytic*r138*','*structural*r144*','*analytic*r137*','t177c143-*','*structural*r143*','t373e135-*','*analytic*r135*','*analytic*r136*','k369r134-*','t088p133-*']
relpaths=[
'frontier/campaigns/2026-10-14/discovery-arithmetic-r107-parent/assessment.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r107/notes/squarefree-feasibility.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r107/READING.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r1/candidate.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r41/screen021/checkpoint.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r19/payload/screen182.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r19/checkpoint.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r7/checkpoint.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r7/reading.md',
'frontier/campaigns/2026-10-14/spin-four-factor-r2/original-scope.md',
'frontier/iterations/i99-quantitative-arithmetic-patterns-discovery.md',
'frontier/iterations/i104-modular-representation-discovery.md']
earlier={}
for name in ['history-search.json','history-search-refined.json','history-search-polynomial.json','history-search-visible.json']:
 data=json.loads((ROOT/'private'/name).read_text())
 for r in data.get('matched_files',[]):
  if r.get('path') in relpaths:
   earlier.setdefault(r['path'],[]).append({'record':name,'sha256':r['sha256']})
records=[]
for rel in relpaths:
 assert not any(fnmatch.fnmatch(c.lower(),p) for c in Path(rel).parts for p in patterns)
 p=PROJECT/rel
 if not p.exists():
  records.append({'path':rel,'status':'missing; no guessed replacement'});continue
 assert not any(q.is_symlink() for q in [p,*p.parents])
 b=p.read_bytes(); h=hashlib.sha256(b).hexdigest()
 dest=ROOT/'private/history/current-originals'/rel
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 records.append({'path':rel,'snapshot':str(dest.relative_to(ROOT)),'bytes':len(b),'sha256':h,'status':'late-current-original-capture','earlier_search_observations':earlier.get(rel,[]),'matches_available_earlier_search':all(e['sha256']==h for e in earlier[rel]) if rel in earlier else None})
(ROOT/'private/current-originals.json').write_text(json.dumps({'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'warning':'Late capture, never first-read preservation; no historical whole-parent claim. Earlier search digest equality does not establish semantic read extent.','records':records},indent=2)+'\n')
print([(r['path'],r['status'],r.get('matches_available_earlier_search')) for r in records])
