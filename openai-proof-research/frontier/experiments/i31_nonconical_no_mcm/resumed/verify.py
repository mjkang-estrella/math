"""Read-only verification. Emits JSON; does not imply mathematical proof acceptance."""
from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[4]
S=ROOT/'frontier/sources/i31_nonconical_no_mcm';NEW=S/'resumed'
sha=lambda b:hashlib.sha256(b).hexdigest()
errors=[];drift=[];counts={}
def check(path,digest,category):
 p=ROOT/path
 if not p.is_file():errors.append(dict(category=category,path=path,error='missing'));return
 got=sha(p.read_bytes())
 if got!=digest:errors.append(dict(category=category,path=path,expected=digest,actual=got))
cp=json.loads((NEW/'inputs/frontier/experiments/i31-interrupted-parent-checkpoint.json').read_text())
for x in cp['files']:check(x['path'],x['sha256'],'preserved_parent_checkpoint')
counts['preserved_parent_checkpoint']=len(cp['files'])
for category,manifest in [('preserved_i28',S/'i28-preservation.json'),('additional_initial',NEW/'additional-initial-preservation.json')]:
 rows=json.loads(manifest.read_text())
 for x in rows:check(x['path'],x['sha256'],category)
 counts[category]=len(rows)
for name,path in [('initial',S/'input-manifest.json'),('resumed',NEW/'input-manifest.json')]:
 rows=json.loads(path.read_text())
 for x in rows:
  check(x['frozen'],x['sha256'],name+'_frozen_input')
  if x['path']=='frontier/TEN-FINDINGS.md':
   got=sha((ROOT/x['path']).read_bytes())
   drift.append(dict(snapshot=name,path=x['path'],frozen=x['sha256'],live=got,changed=got!=x['sha256']))
  else:check(x['path'],x['sha256'],name+'_live_dependency')
 counts[name+'_inputs']=len(rows)
tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());idx={x['path']:x for x in tree['tree']}
cache=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
corpus=json.loads((S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text())
stream=hashlib.sha256()
for f in corpus['files']:
 p=cache/f['path'];b=p.read_bytes();v=sha(b);g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 if v!=f['sha256'] or g!=f['git_blob'] or idx.get(f['path'],{}).get('sha')!=g:errors.append(dict(category='current_corpus_source',path=f['path']))
 stream.update(f['path'].encode()+b'\0'+v.encode()+b'\n')
inv=json.loads((NEW/'inventory-audit.json').read_text())
if stream.hexdigest()!=inv['path_digest_stream_sha256']:errors.append(dict(category='inventory_digest'))
actual={str(p.relative_to(cache)) for p in cache.rglob('*') if p.is_file()}
expected={x['path'] for x in corpus['files']}
if actual!=expected:errors.append(dict(category='corpus_inventory_paths',extra=sorted(actual-expected),missing=sorted(expected-actual)))
roots={x['path'].split('/')[1] for x in tree['tree'] if x['path'].startswith('preprints/')}
counts['corpus_files']=len(corpus['files']);counts['manuscripts']=len(roots)
if len(corpus['files'])!=9340 or len(roots)!=749 or tree.get('truncated',False):errors.append(dict(category='complete_inventory_contract'))
rows=json.loads((S/'pinned-manifest.json').read_text())['files']
for f in rows:
 b=(S/'pinned'/f['path']).read_bytes();g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 if sha(b)!=f['sha256'] or g!=f['git_blob'] or idx[f['path']]['sha']!=g:errors.append(dict(category='pinned_C',path=f['path']))
counts['pinned_C']=len(rows)
contracts=json.loads((NEW/'source-contracts.json').read_text())
for f in contracts:
 if sha(f['exact_statement'].encode())!=f['statement_sha256'] or f['exact_statement'] not in (ROOT/f['path']).read_text():errors.append(dict(category='source_contract',label=f['label']))
counts['source_contracts']=len(contracts)
passages=json.loads((NEW/'read-passages.json').read_text())
for f in passages:
 lines=(ROOT/f['path']).read_text().splitlines(keepends=True);b=''.join(lines[f['start_line']-1:f['end_line']]).encode()
 if sha(b)!=f['sha256']:errors.append(dict(category='read_passage',path=f['path'],start_line=f['start_line']))
counts['read_passages']=len(passages)
for name,mp in [('initial',S/'literature/manifest.json'),('resumed',NEW/'literature/manifest.json')]:
 rows=json.loads(mp.read_text())
 for f in rows:
  if 'path' in f:check(f['path'],f['sha256'],'literature_'+name)
 counts['literature_'+name+'_retrievals']=len(rows)
seal=json.loads((NEW/'artifact-seal.json').read_text())
for f in seal['files']:check(f['path'],f['sha256'],'sealed_candidate_artifact')
counts['sealed_candidate_artifacts']=len(seal['files'])
restart=NEW/'restart-20261011'
recovered=json.loads((restart/'recovered-manifest.json').read_text())
recovered_paths={f['path']:f['frozen'] for f in recovered}
for f in recovered:check(f['frozen'],f['sha256'],'restart_recovered_snapshot')
old_seal=json.loads((restart/'recovered-artifact-seal.json').read_text())
for f in old_seal['files']:
 check(recovered_paths.get(f['path'],f['path']),f['sha256'],'restart_preserved_candidate')
counts['restart_preserved_candidate']=len(old_seal['files'])
retrievals=json.loads((restart/'retrieval-manifest.json').read_text())
for f in retrievals:
 if 'path' in f:check(f['path'],f['sha256'],'restart_primary_retrieval')
 else:errors.append(dict(category='restart_primary_retrieval',url=f['url'],error=f.get('error')))
counts['restart_primary_retrievals']=len(retrievals)
e=ROOT/'frontier/experiments/i31_nonconical_no_mcm/resumed'
r=subprocess.run([sys.executable,str(e/'diagnostics.py')],capture_output=True,text=True)
if r.returncode or json.loads(r.stdout)!=json.loads((e/'diagnostics.json').read_text()):errors.append(dict(category='diagnostic_replay',returncode=r.returncode,stderr=r.stderr))
result=dict(status='PASS integrity and deterministic diagnostics only' if not errors else 'FAIL',counts=counts,errors=errors,shared_ledger_drift=drift,diagnostic_replay=r.returncode==0,mathematical_status='Full author candidate; no independent proof or significance verdict',accepted_count_increment=0,limits='Hashes and finite diagnostics cannot certify the geometric proof. Initial checkpoint, I28, immutable sources and candidate artifacts are distinct checks; shared-ledger drift is informational.')
print(json.dumps(result,indent=2,sort_keys=True))
raise SystemExit(bool(errors))
