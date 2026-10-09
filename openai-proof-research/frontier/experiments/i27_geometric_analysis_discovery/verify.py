from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i27_geometric_analysis_discovery';E=ROOT/'frontier/experiments/i27_geometric_analysis_discovery'
sha=lambda b:hashlib.sha256(b).hexdigest()
errors=[];drift=[];counts={}
def check(ok,msg):
 if not ok:errors.append(msg)
inputs=json.loads((S/'input-manifest.json').read_text())
for x in inputs:
 b=(S/'inputs'/x['path']).read_bytes();check(sha(b)==x['sha256'] and len(b)==x['bytes'],'frozen input '+x['path'])
 live=(ROOT/x['path']).read_bytes()
 if sha(live)!=x['sha256']:
  if x['shared_index']:drift.append({'path':x['path'],'frozen_sha256':x['sha256'],'live_sha256':sha(live)})
  else:errors.append('non-ledger input drift '+x['path'])
counts['frozen_inputs']=len(inputs)
tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());check(not tree.get('truncated',False),'truncated inventory');tb={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'};counts['manuscript_directories']=sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree['tree'])
cm=json.loads((S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text());cache=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
check(cm['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','pin')
for x in cm['files']:
 b=(cache/x['path']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 check(sha(b)==x['sha256'] and len(b)==x['bytes'] and blob==x['git_blob']==tb[x['path']],'corpus '+x['path'])
counts['verified_corpus_texts']=len(cm['files']);counts['verified_corpus_bytes']=sum(x['bytes'] for x in cm['files'])
sm=json.loads((S/'source-manifest.json').read_text())
for x in sm['files']:
 b=(S/'pinned'/x['path']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 check(sha(b)==x['sha256'] and blob==x['git_blob']==tb[x['path']],'selected '+x['path'])
 check(x['url']=='https://raw.githubusercontent.com/openai/math/'+cm['pin']+'/'+x['path'],'source URL '+x['path'])
counts['selected_pinned_files']=len(sm['files'])
contracts=json.loads((S/'source-contracts.json').read_text())
for x in contracts:
 txt=(S/'pinned'/x['path']).read_text();check(x['text'] in txt and sha(x['text'].encode())==x['sha256'],'contract '+x['path'])
counts['statement_inventory']=len(contracts)
for name in ['source-read-passages.json','primary-read-passages.json']:
 rows=json.loads((S/name).read_text())
 for x in rows:
  lines=(ROOT/x['path']).read_text().splitlines(keepends=True);t=''.join(lines[x['start_line']-1:x['end_line']]);check(t==x['text'] and sha(t.encode())==x['sha256'],'passage '+x['path'])
 counts[name]=len(rows)
rows=json.loads((S/'literature/manifest.json').read_text())
for x in rows:
 if 'error' in x:errors.append('retrieval failure '+str(x));continue
 b=(ROOT/x['path']).read_bytes();check(sha(b)==x['sha256'] and len(b)==x['bytes'],'retrieval '+x['path'])
counts['primary_retrievals']=len(rows)
report={'status':'PASS' if not errors else 'FAIL','counts':counts,'shared_index_drift':drift,'errors':errors,'limits':'Integrity/identity and input-drift verification only; not an independent proof/significance review.'}
(E/'verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2));sys.exit(bool(errors))
