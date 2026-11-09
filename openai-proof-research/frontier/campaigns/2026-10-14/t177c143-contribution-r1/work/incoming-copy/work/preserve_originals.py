from pathlib import Path
import hashlib,json,datetime
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r143'
C='frontier/campaigns/2026-10-14/'
paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md','frontier/iterations/i07-structures.md']
paths += [C+p for p in ['discovery-structural-r142-parent/assessment.md','fresh-structural-discovery-r142/packet/public/handoff.md','fresh-structural-discovery-r142/packet/public/prefreeze-derivation.md','fresh-structural-discovery-r142/packet/public/read-and-scope-limits.md','fresh-structural-discovery-r14/screening.md','fresh-structural-discovery-r30/screen-168.md','fresh-structural-discovery-r80/scope-freeze.md','fresh-structural-discovery-r80/proof-attempt.md','fresh-structural-discovery-r110/public/screening.md','fresh-structural-discovery-r111/packet/public/screen-168.md','fresh-structural-discovery-r117/packet/public/structural-screens.md','fresh-structural-discovery-r126/packet/public/other-screens.md']]
def excluded(path):
 for s in Path(path).parts:
  s=s.lower()
  if s.startswith(('t373e135-','k369r134-','t088p133-')) or ('analytic' in s and any(x in s for x in ['r135','r136','r137'])) or ('arithmetic' in s and 'r107' in s):return True
 return False
rows=[]
for rel in paths:
 assert not excluded(rel)
 src=P/rel
 assert src.is_file() and not src.is_symlink(),rel
 data=src.read_bytes()
 out=R/'packet/private/current-originals'/rel
 out.parent.mkdir(parents=True,exist_ok=True)
 out.write_bytes(data)
 rows.append({'original':rel,'copy':str(out.relative_to(R)),'size':len(data),'sha256':hashlib.sha256(data).hexdigest(),'captured':datetime.datetime.now(datetime.timezone.utc).isoformat()})
(R/'packet/private/current-originals-receipt.json').write_text(json.dumps({'status':'LATE current-original snapshots; not initial baseline, not evidence of unchanged bytes before capture; whole files copied privately, semantic read extents separately limited. Mutable routing/ledger contents are observations only.','files':rows},indent=2)+'\n')
print('Late snapshots:',len(rows))
