from pathlib import Path
import hashlib,json,shutil
ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[3]
P=ROOT/'packet/private'; D=P/'history';D.mkdir(exist_ok=True)
paths=[
'frontier/iterations/i60-threshold-structural-combinatorics-discovery.md',
'frontier/iterations/i13-fresh-discovery.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r121/packet/public/other-screens.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r35/matching120.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r30/screen-131.md',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r33/151-technical-screen.md',
'frontier/campaigns/2026-10-14/fresh-parent-discovery-r1/screen.md',
'frontier/campaigns/2026-10-14/fresh-parent-discovery-r7/screen.md',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r93/continuous-time-attempt.md',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r95/rescaled-carrier.md',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r95/stationary-clock.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r44/history-and-comparison.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r44/prefix-law.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r113/packet/public/screen-097.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r25/candidate.md',
'frontier/campaigns/2026-10-14/discovery-structural-r125-parent/contribution-r1-adoption.json',
'frontier/campaigns/2026-10-14/t238b125-contribution-r1/review.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r126/REPORT.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r126/packet/public/report.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r126/packet/public/ising-feasibility.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r126/packet/public/other-screens.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r126/packet/public/reading-limits.md',
'frontier/campaigns/2026-10-14/discovery-structural-r126-parent/intake.json']
for n in range(23,41):
 paths += [str(x.relative_to(REPO)) for x in (REPO/'frontier/findings').glob(f'R{n:03d}-*.md')]
rec=[]
for i,path in enumerate(paths):
 b=(REPO/path).read_bytes();dst=D/f'{i:02d}-{Path(path).name}';dst.write_bytes(b)
 rec.append(dict(source=path,local=str(dst.relative_to(ROOT/'packet')),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),semantic_extent='See public/reading-limits.md; copying is not a complete-reading assertion.'))
(P/'history.json').write_text(json.dumps(rec,indent=2)+'\n')
a=json.loads((P/'search-receipts.json').read_text());selected=[]
for i,r in enumerate(a):
 p=ROOT/'packet'/r['path'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256']
 rows=[]
 for ln in b.decode().splitlines():
  v=ln.split(':',2)
  if len(v)!=3:continue
  path,no,body=v
  if any(path.removeprefix('./')==x for x in paths) or (i==4 and len(body)<1200):
   rows.append(dict(path=path,line=no,snippet=body[:600],truncated=len(body)>600))
 selected.append(dict(query=i,hits=rows))
 r['lines']=b.count(b'\n');r['retained']=False;r['removal_reason']='Large duplicate-heavy raw search output removed after hashing; selected snippets retained, not reconstructible full output.'
 p.unlink()
for p in P.glob('search-selected-*.txt'):p.unlink()
(P/'search-selected.json').write_text(json.dumps(selected,indent=2)+'\n')
(P/'search-receipts.json').write_text(json.dumps(a,indent=2)+'\n')
(P/'session-limits.json').write_text(json.dumps(dict(status='PREFREEZE',frozen_target=None,nominee=None,independent_verdict=None,count_assignment=None,pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',complete_tree_entries=13223,complete_tree_truncated=False,primary_failures=[],navigation_failures=['Initial inventory stripped preprints/ prefix; corrected before acquisition.','Wrong date suffix in local 144 read path; corrected from inventory.','Wrong date suffix in local 097 read path; corrected from inventory.'],search_raw_outputs_removed=True,mathematical_tests=False),indent=2)+'\n')
print('history',len(rec),'source bodies',len(json.loads((P/'canonical.json').read_text())),'primary pairs',len(json.loads((P/'primary/acquisition.json').read_text())))
