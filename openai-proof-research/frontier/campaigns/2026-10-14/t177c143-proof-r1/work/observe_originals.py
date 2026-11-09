from pathlib import Path
import json,hashlib,datetime
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/t177c143-proof-r1'
A=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r143'
def sha(b):return hashlib.sha256(b).hexdigest()
def safe(rel):
 for s in Path(rel).parts:
  s=s.lower()
  assert not any(x in s for x in ['t177c143','t373e135','k369r134','t088p133'])
  assert not ('analytic' in s and any(x in s for x in ['r135','r136','r137']))
  assert not ('arithmetic' in s and 'r107' in s)
  assert not ('structural' in s and 'r144' in s)
rows=json.loads((A/'packet/private/current-originals-receipt.json').read_text())['files']
paths={x['original']:x['sha256'] for x in rows}
for s in ['original-scope.txt','report.md','checkpoint.md']:
 paths['frontier/campaigns/2026-10-14/fresh-analytic-discovery-r41/'+s]=None
obs=[]
for rel,h in paths.items():
 safe(rel);p=P/rel;assert p.is_file() and not p.is_symlink();b=p.read_bytes()
 out=R/'packet/private/current-originals'/rel;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b)
 obs.append({'original':rel,'bytes':len(b),'sha256':sha(b),'author_late_sha256':h,'equal_author_late_snapshot':None if h is None else sha(b)==h,'observed':datetime.datetime.now(datetime.timezone.utc).isoformat(),'copy':str(out.relative_to(R))})
incoming=json.loads((R/'packet/private/incoming-observation.json').read_text())['files']
for x in incoming:
 p=A/x['path'];assert len(p.read_bytes())==x['bytes'] and sha(p.read_bytes())==x['sha256']
out={'meaning':'Late current-original observations only; byte copying/hashing is not semantic reading, does not certify initial bytes, earlier exclusion, whole-parent state, or continued immutability. Original files not edited.','files':obs,'incoming_author_files_still_equal_intake':len(incoming)}
(R/'packet/private/current-originals-observation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'observed_originals':len(obs),'differ_from_author_late':[x['original'] for x in obs if x['equal_author_late_snapshot'] is False],'incoming_still_equal':len(incoming)},indent=2))
