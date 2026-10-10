"""Read-only I39 evidence verification. No network, refreshes, or output files."""
from pathlib import Path
import hashlib,json,re,runpy,sys
from urllib.parse import unquote
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i39_quantum_spectral_discovery';E=Path(__file__).parent
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb';REPORT=R/'frontier/iterations/i39-quantum-spectral-discovery.md'
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def check(ok,msg):
 if not ok:raise AssertionError(msg)
def files_owned():return sorted([REPORT]+[p for d in [S,E] for p in d.rglob('*') if p.is_file() and p!=S/'artifact-seal.json'])
def matches(data,pattern):return [{'line':i,'text':s} for i,s in enumerate(data.decode(errors='replace').splitlines(),1) if pattern.search(s)]
def normalized(rows):return {r['path']:r['matches'] for r in rows}
def main():
 preflight=sys.argv[1:]==['--preflight'];check(preflight or not sys.argv[1:],'Unknown arguments')
 if not preflight:
  seal=read(S/'artifact-seal.json');actual={str(p.relative_to(R)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files_owned()}
  check(actual==seal['files'],'Artifact seal/file-set mismatch')
 inputs=read(S/'inputs.json');drift=[];immutable=0;documented=[]
 known={r['path']:r for r in read(S/'observed-live-drift.json')['changes']}
 for r in inputs:
  check(sha((S/'frozen'/r['path']).read_bytes())==r['sha256'],'Frozen input '+r['path'])
  p=R/r['path'];current=sha(p.read_bytes()) if p.exists() else None
  if r['mutable']:
   if current!=r['sha256']:drift.append({'path':r['path'],'frozen_sha256':r['sha256'],'live_sha256':current})
  elif current==r['sha256']:immutable+=1
  else:
   d=known.get(r['path']);check(d is not None and d['frozen_sha256']==r['sha256'] and d['observed_live_sha256']==current,'Unrecorded immutable input drift '+r['path'])
   check((S/'frozen'/r['path']).read_bytes()==p.read_bytes()+b'\n','Drift is not the documented final newline removal');documented.append(d)
 manifest=read(R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json');check(manifest['pin']==PIN,'Pin')
 tree=read(R/'sources/preprints-tree.json');check(not tree['truncated'],'Truncated tree');index={r['path']:r for r in tree['tree']}
 check(len(tree['tree'])==13223,'Tree count');manuscripts={p.split('/')[1] for p in index if p.startswith('preprints/')};check(len(manuscripts)==749,'Manuscript count')
 audit=[read(S/'corpus-search.json'),read(S/'corpus-targeted-search.json')];pats=[{k:re.compile(v,re.I) for k,v in a['patterns'].items()} for a in audit];found=[{k:[] for k in ps} for ps in pats]
 root=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus';total=0;allrows={}
 for row in manifest['files']:
  path=row['path'];data=(root/path).read_bytes();allrows[path]=row;total+=len(data)
  check(len(data)==row['bytes'] and sha(data)==row['sha256'],'Corpus bytes '+path)
  git=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  check(git==row['git_blob']==index[path]['sha'],'Git identity '+path)
  check(unquote(row['url'])=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path,'Raw URL '+path)
  for ps,out in zip(pats,found):
   for k,p in ps.items():
    hit=matches(data,p)
    if hit:out[k].append({'path':path,'matches':hit})
 check(len(allrows)==9340 and total==141349121,'Corpus coverage')
 check({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==set(allrows),'Corpus file inventory')
 for expected,actual in zip(audit,found):
  for k in actual:check(normalized(actual[k])==normalized(expected['matches'][k]),'Corpus search '+k)
 project=read(S/'project-search-complete.json');pp=re.compile(project['pattern'],re.I);hits=[]
 bindings={r['path']:r for r in read(S/'project-search-ledger-bindings.json')}
 for path in project['files']:
  snapshot=R/bindings[path]['search_snapshot'] if path in bindings else S/'frozen'/path
  data=snapshot.read_bytes()
  if path in bindings:check(sha(data)==bindings[path]['sha256'],'Search ledger snapshot '+path)
  hit=matches(data,pp)
  if hit:hits.append({'path':path,'matches':hit})
 check(len(project['files'])==158 and normalized(hits)==normalized(project['matches']),'Project search')
 selected=read(S/'selected-pinned.json')
 for r in selected:check(r==allrows[r['path']],'Selected pin '+r['path'])
 responses=[];raw=0
 for p in sorted((S/'literature').glob('*.response.json')):
  r=read(p);body=S/'literature'/r['name'];data=body.read_bytes()
  check(r['status']==200 and len(data)==r['bytes'] and sha(data)==r['sha256'],'HTTP body '+r['name'])
  if r['name'].startswith('pinned-'):
   key=r['url'].split('/'+PIN+'/')[1];check(data==(root/key).read_bytes(),'Pinned response '+key);raw+=1
  responses.append(r)
 check(len(responses)==28 and raw==8,'Response coverage')
 versions=read(S/'literature/versions.json');check(len(versions)==10,'Version count')
 for r in versions:
  text=(S/'literature'/(r['name']+'-current.html')).read_text();ident=re.search(r'citation_arxiv_id" content="([^"]+)',text).group(1);v=max(map(int,re.findall(r'\[v(\d+)\]',text)))
  check(ident==r['id'] and v==r['version'],'Version '+r['name'])
  pdf=r['name']+'-v'+str(v)+'.pdf';meta=read(S/'literature'/(pdf+'.response.json'))
  check(meta['url']=='https://arxiv.org/pdf/'+ident+'v'+str(v),'Version PDF URL '+pdf)
 readlog=read(S/'read-passages.json')
 for r in readlog['passages']:
  data=(R/r['path']).read_bytes();check(sha(data)==r['sha256'],'Read file '+r['path']);lines=data.decode(errors='replace').splitlines()
  for span in r['ranges']:
   text='\n'.join(lines[span['first_line']-1:span['last_line']]);check(sha(text.encode())==span['sha256_utf8_joined_lines'],'Read range '+r['path']);check(re.findall(r'\\label\{([^}]+)\}',text)==span['labels'],'Read labels')
  if 'pinned_identity' in r:check(r['pinned_identity']==allrows[r['pinned_identity']['path']],'Read pin')
 for r in readlog['visual_checks']:check(sha((R/r['path']).read_bytes())==r['sha256'],'Visual '+r['path'])
 for i in range(1,5):
  w=read(S/('web0'+str(i)+'.json'));check('request' in w and 'response' in w and w['request']['search_query'],'Web request snapshot')
 diag=runpy.run_path(str(E/'check.py'))['check']();check(json.loads(json.dumps(diag,default=str))==read(E/'diagnostics.json'),'Diagnostic replay');check(diag['exact_assertions']==389,'Exact check count')
 check(read(S/'contracts.json')['pin']==PIN,'Contracts pin')
 return {'status':'PASS preflight' if preflight else 'PASS sealed read-only verification','artifact_files':len(files_owned()),'frozen_inputs':len(inputs),'immutable_live_inputs_unchanged':immutable,'live_mutable_drift':drift,'documented_nonpremise_live_drift':documented,'corpus_files':len(allrows),'corpus_bytes':total,'tree_entries':len(index),'manuscripts':len(manuscripts),'project_search_files':158,'project_matched_documents':len(hits),'selected_source_files':len(selected),'selected_manuscripts':len({r['path'].split('/')[1] for r in selected}),'primary_and_raw_responses':len(responses),'fresh_pinned_responses':raw,'versioned_primary_pdfs':len(versions),'read_records':len(readlog['passages']),'exact_checks':diag['exact_assertions'],'verdict':'Evidence integrity and scoped exact diagnostics only. No substantial finding nominated; H unproved and not refuted.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
