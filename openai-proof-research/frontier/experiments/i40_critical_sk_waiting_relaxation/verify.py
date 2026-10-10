"""Read-only evidence reproduction. No retrievals, rewrites, or seal refreshes."""
from pathlib import Path
import hashlib,json,re,runpy
from urllib.parse import unquote
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i40_critical_sk_waiting_relaxation'
E=R/'frontier/experiments/i40_critical_sk_waiting_relaxation'
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def checkbytes(p,row):
 b=p.read_bytes()
 assert len(b)==row['bytes'] and sha(b)==row['sha256'],str(p)
 return b
def ownfiles():
 ps=[R/'frontier/iterations/i40-critical-sk-waiting-relaxation.md']
 ps+=list(S.rglob('*'))+list(E.rglob('*'))
 return sorted(str(p.relative_to(R)) for p in ps if p.is_file() and p!=S/'artifact-seal.json')
def verify():
 out={'status':'PASS evidence integrity and finite diagnostics only','pin':PIN}
 seal=read(S/'artifact-seal.json')
 assert set(ownfiles())==set(seal['files']),'I40 artifact membership changed'
 for p,row in seal['files'].items():checkbytes(R/p,row)
 out['sealed_artifacts']=len(seal['files'])
 drift=[];inputs=read(S/'inputs.json')
 for row in inputs:
  checkbytes(S/'frozen'/row['path'],row)
  b=(R/row['path']).read_bytes()
  if len(b)!=row['bytes'] or sha(b)!=row['sha256']:
   record={'path':row['path'],'baseline_sha256':row['sha256'],'live_sha256':sha(b),'mutable':row['mutable']}
   assert row['mutable'],record
   drift.append(record)
 out['frozen_inputs']=len(inputs);out['mutable_ledger_drift']=drift
 prior=read(S/'frozen/frontier/sources/i39_quantum_spectral_discovery/artifact-seal.json')
 for p,row in prior['files'].items():checkbytes(R/p,row)
 out['unchanged_I39_sealed_artifacts']=len(prior['files'])
 tree=read(S/'frozen/sources/preprints-tree.json')
 assert tree['truncated'] is False and len(tree['tree'])==13223
 manuscripts={r['path'].split('/')[1] for r in tree['tree'] if r['path'].startswith('preprints/') and len(r['path'].split('/'))>=2}
 assert len(manuscripts)==749
 blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
 manifest=read(S/'frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
 assert manifest['pin']==PIN
 indexed={r['path']:r for r in manifest['files']}
 actual={str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}
 assert actual==set(indexed) and len(actual)==9340
 audit=read(S/'corpus-search.json');matches={k:[] for k in audit['patterns']};total=0
 for row in manifest['files']:
  b=checkbytes(C/row['path'],row);total+=len(b)
  git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert git==row['git_blob']==blobs[row['path']]
  assert unquote(row['url'])=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+row['path']
  for k,pat in audit['patterns'].items():
   hits=[{'line':i,'text':v} for i,v in enumerate(b.decode(errors='replace').splitlines(),1) if re.search(pat,v,re.I)]
   if hits:matches[k].append({'path':row['path'],'matches':hits})
 assert total==141349121 and matches==audit['matches']
 out['corpus']={'files':len(actual),'bytes':total,'tree_entries':len(tree['tree']),'manuscripts':len(manuscripts),'sha256_and_git_blobs':'all reproduced','search_hits':{k:len(v) for k,v in matches.items()}}
 project=read(S/'project-search.json');hits=[]
 for path in project['files']:
  lines=(S/'frozen'/path).read_text().splitlines()
  found=[{'line':i,'text':v} for i,v in enumerate(lines,1) if re.search(project['pattern'],v,re.I)]
  if found:hits.append({'path':path,'matches':found})
 assert hits==project['matches']
 out['project_search']={'files':len(project['files']),'matched_documents':len(hits)}
 selected=read(S/'selected-pinned.json')
 for row in selected:assert row==indexed[row['path']]
 out['selected_sources']={'files':len(selected),'manuscripts':len({r['path'].split('/')[1] for r in selected})}
 passages=read(S/'read-passages.json')
 for row in passages:
  b=(R/row['path']).read_bytes();assert sha(b)==row['sha256']
  ls=b.splitlines(keepends=True)
  for span in row['ranges']:
   assert 1<=span['first']<=span['last']<=len(ls)
   assert sha(b''.join(ls[span['first']-1:span['last']]))==span['sha256']
 contracts=read(S/'contracts.json')
 for row in contracts:
  m=indexed[row['source_path']]
  assert row['raw_url']==m['url'] and row['git_blob']==m['git_blob'] and row['file_sha256']==m['sha256']
  ls=(C/row['source_path']).read_bytes().splitlines(keepends=True)
  assert ('\\label{'+row['label']+'}').encode() in ls[row['label_line']-1]
  b=b''.join(ls[row['excerpt_first']-1:row['excerpt_last']])
  assert sha(b)==row['excerpt_sha256'] and b.decode()==row['excerpt']
 out['read_passages']=len(passages);out['source_contract_labels']=len(contracts)
 responses=[];fresh=0
 for p in sorted((S/'literature').glob('*.response.json')):
  row=read(p);b=checkbytes(S/'literature'/row['name'],row)
  assert row['status']==200,row
  if row['url'].startswith('https://raw.githubusercontent.com/openai/math/'):
   path=row['url'].split('/'+PIN+'/')[1];assert sha(b)==indexed[path]['sha256'];fresh+=1
  if row['name'].endswith('.pdf'):assert b.startswith(b'%PDF-')
  responses.append(row)
 versions=read(S/'literature/versions.json')+[{'name':'chatterjee-correct','id':'math/0508519','version':3}]
 for row in versions:
  b=(S/'literature'/(row['name']+'-current.html')).read_bytes()
  assert max(map(int,re.findall(rb'\[v(\d+)\]',b)))==row['version']
  pdfname=row['name']+'-v'+str(row['version'])+'.pdf'
  response=read(S/'literature'/(pdfname+'.response.json'))
  assert response['url']=='https://arxiv.org/pdf/'+row['id']+'v'+str(row['version'])
  convert=read(S/'literature'/(pdfname+'.pdftotext.json'));assert convert['returncode']==0
  assert (S/'literature'/(pdfname+'.txt')).stat().st_size>100
 out['primary_responses']={'total':len(responses),'fresh_pinned':fresh,'versioned_pdfs':len(versions),'identity_error_retained':read(S/'literature/retrieval-assessment.json')['wrong_identity_retained']}
 for name in ['web01.json','web02.json']:
  x=read(S/name);assert x
 diagnostic=runpy.run_path(str(E/'check.py'))['check']()
 assert diagnostic==read(E/'diagnostics.json')
 out['diagnostics']=diagnostic
 out['scope']='No independent analytic proof/significance verdict. Full W remains unproved/unrefuted; Gaussian deduction is technical and awaits parent review.'
 return out
if __name__=='__main__':print(json.dumps(verify(),indent=2))
