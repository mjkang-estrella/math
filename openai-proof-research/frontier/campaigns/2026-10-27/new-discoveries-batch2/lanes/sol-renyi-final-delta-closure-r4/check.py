import json,hashlib,re,pathlib,collections
from work import O,BASE,HEAD,sha

def load(n):return json.loads((O/n).read_text())
def blob(raw):return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
def added(f):
 raw=('\n'.join(l[1:] for l in f['patch'].splitlines() if l.startswith('+'))+'\n').encode()
 if blob(raw)!=f['sha']:raw=raw[:-1]
 assert blob(raw)==f['sha']
 return raw

def verify():
 dag=load('dag.json');src=pathlib.Path(dag['source']);assert sha(src)==dag['sha256'];orig=json.loads(src.read_text())
 assert orig['behind_by']==0 and orig['merge_base_commit']['sha']==BASE and len(orig['commits'])==orig['ahead_by']==28
 cs={c['sha']:c for c in orig['commits']};chain=dag['first_parent_chain'];assert chain[0]==BASE and chain[-1]==HEAD
 for a,b in zip(chain,chain[1:]):assert cs[b]['parents'][0]['sha']==a
 logs=[json.loads(l) for l in (O/'http.jsonl').read_text().splitlines()]
 for r in logs:assert r['status']==200 and sha(O/r['file'])==r['sha256'] and (O/r['file']).stat().st_size==r['bytes']
 steps=load('steps.json'); entries=[]; commits=[]
 for i,r in enumerate(steps):
  d=load(r['response']);assert sha(O/r['response'])==r['sha256']
  assert r['base']==chain[i] and r['head']==chain[i+1]
  assert d['base_commit']['sha']==r['base'] and d['merge_base_commit']['sha']==r['base'] and d['behind_by']==0 and d['status']=='ahead'
  assert len(d['commits'])==d['ahead_by']==d['total_commits']<250
  commits.extend(c['sha'] for c in d['commits'])
  if i==3:
   pages=sorted((O/'responses').glob('commit03-page*.json'));assert len(pages)==4;fs=[]
   for k,p in enumerate(pages):
    j=json.loads(p.read_text());assert j['sha']==r['head'] and j['parents'][0]['sha']==r['base']
    assert len(j['files'])==(100 if k<3 else 79)
    row=next(x for x in logs if x['file']==str(p.relative_to(O)))
    link=next((v for key,v in row['headers'].items() if key.lower()=='link'),'')
    assert ('rel="next"' in link)==(k<3)
    fs.extend(j['files'])
   assert len(fs)==len({f['filename'] for f in fs})==379<3000
   assert {f['filename'] for f in d['files']}=={f['filename'] for f in fs[:300]}
  else:
   assert len(d['files'])<300;fs=d['files']
  entries.extend({'step':i,'head':r['head'],'base':r['base'],**f} for f in fs)
 assert len(commits)==len(set(commits))==28 and set(commits)==set(cs)
 assert entries==load('path-entries.json') and len(entries)==len({f['filename'] for f in entries})==538
 rawrows={r['entry']:r for r in load('raw-bodies.json')};recon={r['entry']:r for r in load('reconstructed-bodies.json')}
 for i,f in enumerate(entries):
  patch=f['patch'];assert patch
  # Count actual changed lines independently of declared file counters.
  assert sum(l.startswith('+') for l in patch.splitlines())==f['additions']
  assert sum(l.startswith('-') for l in patch.splitlines())==f['deletions']
  chunks=re.split(r'(?m)^@@ ',patch)[1:];assert chunks
  for chunk in chunks:
   header,*lines=chunk.splitlines();m=re.match(r'-(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',header);assert m
   old=int(m[2] or 1);new=int(m[4] or 1)
   assert sum(l.startswith((' ','-')) for l in lines)==old
   assert sum(l.startswith((' ','+')) for l in lines)==new
  if f['status']=='added':
   raw=added(f);assert hashlib.sha256(raw).hexdigest()==recon[i]['sha256']
  else:
   r=rawrows[i];raw=(O/r['file']).read_bytes();assert blob(raw)==f['sha']==r['git_blob'] and hashlib.sha256(raw).hexdigest()==r['sha256']
 for q in (O/'bodies').glob('selected-*.txt'):
  i=int(q.stem.split('-')[1]);assert q.read_bytes()==added(entries[i])
 for label in ['candidate','review']:
  before=load('freeze-before.json')[label];after=load('freeze-after.json')[label]
  assert before==after
  for k,v in before['files'].items():assert sha(pathlib.Path(before['root'])/k)==v
 assert load('freeze-after.json')['helper_guard_sha256']=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
 manifest=load('finalmanifest.json')
 for k,v in manifest['files'].items():assert sha(O/k)==v
 return {'result':'PASS','first_parent_steps':9,'commit_metadata_union':28,'unique_mainline_changed_paths':538,'added_complete_git_blob_verified':525,'modified_immutable_body_git_blob_verified':13,'candidate_frozen_paths':347,'review_frozen_paths':208,'scope':'complete first-parent state-transition coverage; not all transient side-branch versions'}
if __name__=='__main__':print(json.dumps(verify(),indent=2))
