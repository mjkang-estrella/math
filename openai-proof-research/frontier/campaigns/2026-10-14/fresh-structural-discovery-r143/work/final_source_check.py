from pathlib import Path
import hashlib,json,datetime
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r143'
def sha(b):return hashlib.sha256(b).hexdigest()
freeze='cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221'
assert sha((R/'packet/public/frozen-scope.md').read_bytes())==freeze
raw=(R/'packet/private/current-originals/sources/preprints-tree.json').read_bytes()
assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
t=json.loads(raw);assert len(t['tree'])==13223 and not t['truncated']
index={x['path']:x for x in t['tree']}
u=json.loads((R/'packet/private/upstream-acquisition.json').read_text())
for x in u:
 b=(R/'packet/private/upstream'/x['path']).read_bytes();meta=index[x['path']]
 assert len(b)==x['size']==meta['size']
 assert sha(b)==x['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==meta['sha']
prim=json.loads((R/'packet/private/primary/acquisition.json').read_text());n=0
for x in prim:
 if 'failure' in x:continue
 b=(R/'packet/private/primary'/(x['name']+'.pdf')).read_bytes()
 assert len(b)==x['size'] and sha(b)==x['sha256'];n+=1
orig=json.loads((R/'packet/private/current-originals-receipt.json').read_text())
changes=[]
for x in orig['files']:
 for component in Path(x['original']).parts:
  s=component.lower()
  assert not (s.startswith(('t373e135-','k369r134-','t088p133-')) or ('analytic' in s and any(v in s for v in ['r135','r136','r137'])) or ('arithmetic' in s and 'r107' in s))
 b=(P/x['original']).read_bytes();c=(R/x['copy']).read_bytes()
 assert len(c)==x['size'] and sha(c)==x['sha256']
 if b!=c:
  dest=R/'packet/private/current-originals-at-final-check'/x['original']
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  changes.append({'original':x['original'],'earlier_sha256':x['sha256'],'observed_sha256':sha(b),'bytes':len(b),'new_copy':str(dest.relative_to(R))})
receipt={'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'frozen_sha256':freeze,'complete_tree_entries':13223,'raw_source_files_reauthenticated':len(u),'primary_pdf_bytes_rechecked':n,'named_originals_equal_to_late_snapshots_now':len(orig['files'])-len(changes),'changed_observations':changes,'meaning':'Artifact checks only. Late originals equality does not certify first-read bytes or any historical parent state.'}
(R/'packet/private/final-source-check.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
