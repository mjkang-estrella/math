"""Bind only explicitly named originals; no traversal or inherited execution."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent
PROJECT=ROOT.parents[3]
BLOCK=re.compile(r'structural.*r144|arithmetic.*r10[89]|t185r144',re.I)
def hashes(b):
 return {'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'git_blob_sha1_of_bytes':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
items=[
 ('AGENTS.md','full administrative instructions'),
 ('sources/upstream.json','full'),
 ('sources/CONTENTS.md','lines 1-170 plus selected heading navigation; not full catalogue'),
 ('frontier/NEW-TEN-2026-10-14.md','lines 1-180 acceptance rules and context'),
 ('frontier/iterations/i130-spectral-harmonic-discovery.md','harmonic H scope and H1/H2 proof portions; lines 110-205 reread explicitly after freeze; initial combined display truncated outside credited harmonic portions'),
 ('frontier/iterations/i133-fixed-metric-harmonic-growth.md','full; initial display truncation recovered with lines 1-132 and 24-65; lines 132-end reread after freeze'),
 ('frontier/iterations/iteration133-fixed-metric-harmonic-growth-task.json','decoded brief lines 236-375 FINALPARENTI130 response; other fields navigation only; not full task-body reading'),
 ('frontier/iterations/iteration136-birational-positivity-discovery-task.json','decoded brief lines 381-481 FINALPARENTI133 response; other fields navigation only; not full task-body reading'),
 ('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r33/report.md','full; named completed original on harmonic Source361 overlap'),
 ('frontier/campaigns/2026-10-14/discovery-analytic-r137-parent/assessment.md','full; explicit user-directed completed-original exception'),
 ('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r137/DERIVATION.md','full with initial display truncation recovered by lines 95-145; explicit user-directed completed-original exception'),
 ('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r137/READING-LIMITS.md','full; explicit user-directed completed-original exception'),
 ('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r137/NOTES.md','full; explicit user-directed completed-original exception'),
]
old=json.loads((ROOT/'private/history-search.json').read_text())
scanned={x['path']:x for x in old['admitted']}
out=[]
for rel,extent in items:
 if any(BLOCK.search(x) for x in Path(rel).parts): raise ValueError('isolated path')
 b=(PROJECT/rel).read_bytes(); dest=ROOT/'private/originals'/rel
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 row={'canonical_project_path':rel,'local_snapshot':str(dest.relative_to(ROOT)),**hashes(b),'lines':len(b.decode().splitlines()),'read_extent':extent,'snapshot_timing':'after author proof development; does not establish original bytes at earlier reading'}
 if rel in scanned: row['matches_retained_search_sha256']=row['sha256']==scanned[rel]['sha256']
 out.append(row)
(ROOT/'original-ledger.json').write_text(json.dumps(out,indent=2)+'\n')
s=json.loads((ROOT/'source-ledger.json').read_text())
for x in s:
 p=x['canonical_path'];name=Path(p).name
 if 'September-26' in p and '/sections/' in p:
  x['read_extents']=[{'lines':[1,x['lines']],'timing':'before freeze; matching lines 1-255 also reread during proof development'}]
 elif 'September-25' in p and name=='introduction.tex':
  x['read_extents']=[{'lines':[1,130],'timing':'before freeze'},{'lines':[131,189],'timing':'late, after proof development'}]
 elif 'September-25' in p and name=='finite-selection.tex':
  x['read_extents']=[{'lines':[1,94],'timing':'before freeze'}]
 elif 'September-25' in p and name=='transmission.tex':
  x['read_extents']=[{'lines':[1,45],'timing':'late, after proof development'},{'lines':[503,758],'timing':'late, after proof development'}]
 x['unlisted_ranges']='downloaded, not credited as body reading'
(ROOT/'source-ledger.json').write_text(json.dumps(s,indent=2)+'\n')
p=json.loads((ROOT/'primary-ledger.json').read_text())
ranges={'2109.07534v1':[(275,355),(753,1057)],'1601.02066v1':[(470,595)],'1108.3244v3':[(149,181),(199,304)],'2312.16939v4':[(1002,1038)]}
for x in p:
 x['read_extents']=[{'file':x['extracts'][0]['path'],'lines':list(y),'timing':'before freeze'} for y in ranges[x['id']]]
 if x['id']=='1601.02066v1': x['read_extents'].append({'file':x['extracts'][0]['path'],'lines':[418,469],'timing':'late, after proof development'})
 x['unlisted_ranges']='navigation snippets only or unread; downloaded bytes are not full reading'
 x['access_failures']=[]
(ROOT/'primary-ledger.json').write_text(json.dumps(p,indent=2)+'\n')
print('Recorded',len(out),'named originals;',len(s),'source files;',len(p),'primary versions.')
