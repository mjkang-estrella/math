from pathlib import Path
import json,hashlib,shutil,re
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i24_elementary_unimodality'; C=R/'frontier/sources/i14_spectral_width_novelty_r3'
def sha(b):return hashlib.sha256(b).hexdigest()
def put(p,b):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
inputs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/TEN-FINDINGS.md','frontier/iterations/i19-fresh-structural-discovery.md','frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json']
records=[]
for p in inputs:
 b=(R/p).read_bytes();put(S/'inputs'/p,b);records.append(dict(path=p,sha256=sha(b),bytes=len(b)))
(S/'inputs.json').write_text(json.dumps(records,indent=2)+'\n')
m=json.loads((C/'corpus-manifest.json').read_text()); tree={x['path']:x for x in json.loads((R/'sources/preprints-tree.json').read_text())['tree']}
terms=['Lefschetz','unimodal','Hessenberg','chromatic quasisymmetric','quantum theta','scattering diagram','Young permutation']
hits=[];selected=[]
for x in m['files']:
 p=x['path'];b=(C/'corpus'/p).read_bytes();t=b.decode(errors='replace');matches=[]
 for i,line in enumerate(t.splitlines(),1):
  ts=[q for q in terms if q.lower() in line.lower()]
  if ts:matches.append(dict(line=i,terms=ts,text=line))
 if matches:hits.append(dict(path=p,matches=matches))
 if 'Elementary-Positivity-of-Chromatic' in p or ('Hikita-conjecture-for-arbitrary-quivers' in p):
  assert sha(b)==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==tree[p]['sha']
  put(S/'pinned'/p,b);selected.append(x)
(S/'corpus-search.json').write_text(json.dumps(dict(terms=terms,files_scanned=len(m['files']),hits=hits),indent=2)+'\n')
(S/'pinned-manifest.json').write_text(json.dumps(dict(pin=m['pin'],files=selected),indent=2)+'\n')
print('frozen',len(records),'selected',len(selected),'hit files',len(hits))
print('\n'.join(sorted(set(x['path'].split('/')[1] for x in hits))))
