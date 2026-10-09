"""Offline integrity/reproduction; no regeneration of the seal or prior artifacts."""
from pathlib import Path
import json,hashlib,re,subprocess,sys
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i37_supergeometric_avoidance'
X=R/'frontier/experiments/i37_supergeometric_avoidance'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def checked(path,expected):
 b=(R/path).read_bytes();assert sha(b)==expected,('hash',path);return b
def verify():
 seal=read(S/'artifact-seal.json')
 for row in seal['files']:checked(row['path'],row['sha256'])
 drift=[];inputs=read(S/'input-manifest.json')
 for row in inputs:
  if 'frozen' in row:checked(row['frozen'],row['sha256'])
  actual=sha((R/row['path']).read_bytes())
  if row['mutable']:
   if actual!=row['sha256']:drift.append(dict(path=row['path'],baseline=row['sha256'],current=actual))
  else:assert actual==row['sha256'],('immutable input drift',row['path'])
 entries=read(R/'sources/preprints-tree.json')['tree'];by={e['path']:e for e in entries}
 pins=read(S/'pinned-manifest.json')
 for p in pins:
  b=checked(p['local'],p['sha256']);blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert blob==p['git_blob'];entry=by.get(p['path']) or by.get(p['path'].removeprefix('preprints/'));assert entry['sha']==blob
  assert p['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+p['path']
 passages=read(S/'read-passages.json')
 for p in passages:
  b=checked(p['path'],p['file_sha256']);lines=b.decode().splitlines(keepends=True)
  assert sha(''.join(lines[p['first_line']-1:p['last_line']]).encode())==p['passage_sha256']
 for p in read(S/'visual-read-pages.json'):checked(p['path'],p['sha256'])
 contracts=read(S/'source-contracts.json')
 for c in contracts:
  assert c['statement'] in (R/c['path']).read_text();assert sha(c['statement'].encode())==c['sha256']
 responses=read(S/'literature/manifest.json')+read(S/'literature/extra-manifest.json')
 for p in responses:
  if 'path' in p:assert len(checked(p['path'],p['sha256']))==p['bytes']
 prior=read(R/'frontier/sources/i36_common_geometric_avoidance_novelty_r3/literature/manifest.json')
 priorby={p['name']:p for p in prior};same=0
 for p in responses:
  if p.get('same_as_prior'):
   assert (R/p['path']).read_bytes()==(R/priorby[p['name']]['path']).read_bytes();same+=1
 audit=read(S/'inventory-search.json');cm=read(R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
 cache=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus';hits=[];total=0
 for p in cm['files']:
  b=checked(str((cache/p['path']).relative_to(R)),p['sha256']);total+=len(b)
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();e=by.get(p['path']) or by.get(p['path'].removeprefix('preprints/'))
  assert blob==p['git_blob']==e['sha'];linehits=[]
  for i,line in enumerate(b.decode().splitlines(),1):
   patterns=[pat for pat in audit['patterns'] if re.search(pat,line,re.I)]
   if patterns:linehits.append(dict(line=i,text=line,patterns=patterns))
  if linehits:hits.append(dict(path=p['path'],sha256=sha(b),hits=linehits))
 assert hits==audit['hits']
 manuscripts=sorted({e['path'].removeprefix('preprints/').split('/')[0] for e in entries if '/' in e['path'].removeprefix('preprints/')})
 assert manuscripts==audit['manuscripts'] and len(manuscripts)==749
 assert len(entries)==audit['entry_count']==13223 and len(cm['files'])==audit['cache_files']==9340 and total==audit['cache_bytes']==141349121
 result=subprocess.run([sys.executable,'-B',str(X/'checks.py')],capture_output=True,check=True)
 assert result.stdout==(X/'checks.json').read_bytes(),'diagnostic reproduction'
 # Check that the owned directories contain no unexpected unsealed files.
 owned=[R/'frontier/iterations/i37-supergeometric-avoidance.md']+[p for root in [S,X] for p in root.rglob('*') if p.is_file()]
 excluded={S/'artifact-seal.json',X/'verification.json'}
 assert {str(p.relative_to(R)) for p in owned if p not in excluded}=={p['path'] for p in seal['files']}
 return dict(status='PASS',scope='Evidence integrity and exact finite diagnostics, NOT independent proof/significance certification. Target C remains unproved.',sealed_files=len(seal['files']),inputs=len(inputs),pins=len(pins),passages=len(passages),contracts=len(contracts),visual_pages=9,fresh_http_responses=len(responses),fresh_http_failures=[p for p in responses if 'error' in p],identical_prior_responses=same,web_payloads=3,corpus=dict(entries=len(entries),manuscripts=len(manuscripts),files=len(cm['files']),bytes=total,matching_files=len(hits)),diagnostics=json.loads(result.stdout),shared_ledger_drift=drift)
if __name__=='__main__':
 result=verify();out=json.dumps(result,indent=2,ensure_ascii=False)+'\n';(X/'verification.json').write_text(out);print(out,end='')
