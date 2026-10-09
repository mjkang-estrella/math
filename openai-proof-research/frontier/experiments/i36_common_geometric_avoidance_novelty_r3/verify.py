"""Read-only verification except for this review's own final verification.json.
Does not fetch network resources or regenerate any seal.
"""
from pathlib import Path
import contextlib,hashlib,io,json,runpy,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i36_common_geometric_avoidance_novelty_r3'
E=ROOT/'frontier/experiments/i36_common_geometric_avoidance_novelty_r3'
def digest(b):return hashlib.sha256(b).hexdigest()
def read(name):return json.loads((S/name).read_text())
def main():
 seal=read('artifact-seal.json');actual=set()
 for base in (S,E):
  actual.update(str(p.relative_to(ROOT)) for p in base.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p not in (S/'artifact-seal.json',E/'verification.json'))
 actual.add('frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md')
 assert actual=={r['path'] for r in seal['files']},'Owned file inventory changed'
 for r in seal['files']:
  b=(ROOT/r['path']).read_bytes();assert len(b)==r['bytes'] and digest(b)==r['sha256'],r['path']
 shared=[];generated=[];frozen_count=0
 for r in read('input-manifest.json'):
  current=digest((ROOT/r['path']).read_bytes())
  frozen=S/'frozen'/r['path']
  if frozen.exists():assert digest(frozen.read_bytes())==r['sha256'];frozen_count+=1
  if current!=r['sha256']:
   row={'path':r['path'],'baseline':r['sha256'],'current':current}
   if r['mutable']:shared.append(row)
   elif r['path'].endswith('/verification.json'):generated.append(row)
   else:raise AssertionError(row)
 tree=json.loads((ROOT/'sources/preprints-tree.json').read_text());entries={r['path']:r for r in tree['tree']};assert tree['truncated'] is False
 for r in read('pinned-manifest.json'):
  b=(ROOT/r['local']).read_bytes()
  assert len(b)==r['bytes'] and digest(b)==r['sha256']
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']==entries[r['path']]['sha']
  assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in r['url']
 for r in read('read-passages.json'):
  b=(ROOT/r['path']).read_bytes();assert digest(b)==r['file_sha256']
  part=b if r['kind']=='image' else ''.join(b.decode().splitlines(keepends=True)[r['start']-1:r['end']]).encode()
  assert digest(part)==r['passage_sha256']
 for r in read('literature/manifest.json'):
  assert r['status']==200 and 'failure' not in r
  b=(ROOT/r['path']).read_bytes();assert len(b)==r['bytes'] and digest(b)==r['sha256']
 for r in read('primary-equivalence.json'):
  b=(ROOT/r['fresh']).read_bytes();assert b==(ROOT/r['read_copy']).read_bytes() and digest(b)==r['sha256']
 task=json.loads((S/'frozen/frontier/iterations/iteration36-common-geometric-avoidance-novelty-r3-task.json').read_text())
 assert (S/'full-brief.txt').read_text()==task['brief']
 out=io.StringIO()
 with contextlib.redirect_stdout(out):runpy.run_path(str(E/'corpus_screen.py'),run_name='__main__')
 corpus=json.loads(out.getvalue());assert corpus==read('corpus-screen.json')
 checks=runpy.run_path(str(E/'reduction_checks.py'))['run']();assert checks==json.loads((E/'reduction-checks.json').read_text())
 prior=runpy.run_path(str(E/'reproduce_prior.py'))['reproduce']()
 baseline=json.loads((E/'prior-reproduction.json').read_text())
 assert prior['status']=='PASS' and prior['monitored_files_unchanged']==151
 # Prior generated verification outputs are separately reportable; mathematical files must stay fixed.
 pd=[]
 for path,h in baseline['before_after_sha256'].items():
  if prior['before_after_sha256'][path]!=h:
   assert path.endswith('/verification.json');pd.append(path)
 return {'status':'PASS','recommendation':'TECHNICAL ONLY','proof_disposition':'Original R2 PASS without repairs retained','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','sealed_owned_files':len(seal['files']),'bound_inputs':len(read('input-manifest.json')),'frozen_snapshots':frozen_count,'pinned_files':len(read('pinned-manifest.json')),'read_passages':len(read('read-passages.json')),'fresh_http_responses':len(read('literature/manifest.json')),'identical_primary_pdfs':len(read('primary-equivalence.json')),'web_response_snapshots':len(list(S.glob('web-search-*.json'))),'corpus':{k:corpus[k] for k in ('tree_entries','manuscripts','text_files','bytes_read_and_verified')},'diagnostics':checks,'prior_reproduction':{'status':prior['status'],'monitored_files_unchanged':prior['monitored_files_unchanged'],'result':prior['result']},'shared_ledger_drift_since_r3_start':shared,'generated_report_drift_since_r3_start':generated,'prior_generated_file_drift':pd,'scope':'Integrity and exact finite formula checks; significance reasons and universal proof disposition are in the written review.'}
if __name__=='__main__':
 result=main();text=json.dumps(result,indent=2,sort_keys=True)+'\n';(E/'verification.json').write_text(text);print(text,end='')
