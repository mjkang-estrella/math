"""Verify frozen candidate, all author provenance, actual R2 source ranges, and live inputs.
Writes only the R2 directory. Never runs the author's mutating verifier.
"""
from pathlib import Path
import json,hashlib
BASE=Path(__file__).resolve().parents[3]
SRC=BASE/'frontier/sources/i17_six_point_ramsey_r2';FROZEN=SRC/'inputs'
OLD=Path('frontier/sources/i17_fresh_discovery');errors=[];counts={};live_changes=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def ck(ok,msg):
 if not ok:errors.append(msg)
def read(rel):return json.loads((FROZEN/rel).read_text())
def filecheck(rel,digest,size=None):
 b=(FROZEN/rel).read_bytes();ck(sha(b)==digest,'hash '+str(rel));ck(size is None or len(b)==size,'size '+str(rel));return b
inputs=json.loads((SRC/'input-manifest.json').read_text())
for it in inputs:
 b=(BASE/it['snapshot']).read_bytes();ck(sha(b)==it['sha256'],'snapshot '+it['path']);ck(len(b)==it['bytes'],'snapshot size '+it['path'])
 live=BASE/it['path']
 if not live.is_file() or sha(live.read_bytes())!=it['sha256']:live_changes.append(it['path'])
counts['r2_input_snapshots']=len(inputs)
report=FROZEN/'frontier/iterations/i17-fresh-discovery.md'
ck(sha(report.read_bytes())=='87b86401ed5c1d554715c78fa203e33acb0117fd8255357e495a882842c0feb8','candidate supplied hash');ck(len(report.read_text().splitlines())==367,'candidate line count')
inv=read(OLD/'inputs/sources/preprints-tree.json');entries={x['path']:x for x in inv['tree']};ck(inv['truncated'] is False,'inventory truncation')
ck(read(OLD/'complete-inventory-screen.json')['all_entries']==inv['tree'],'inventory screen')
counts['inventory_entries']=len(entries)
manifest=read(OLD/'pinned-manifest.json');by_local={x['local']:x for x in manifest}
for it in manifest:
 b=filecheck(it['local'],it['sha256'],it['bytes']);blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 ck(blob==it['git_blob']==entries[it['path']]['sha'],'git '+it['path'])
 ck(it['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+it['path'],'URL '+it['path'])
counts['author_pinned_blobs']=len(manifest)
for name in ['theorem-contracts.json','read-ranges.json']:
 items=read(OLD/name)
 for it in items:
  lines=(FROZEN/it['local']).read_text().splitlines(keepends=True);passage=''.join(lines[it['start_line']-1:it['end_line']]);ck(it['git_blob']==by_local[it['local']]['git_blob'],'range source')
  if 'exact_statement' in it:
   ck(it['exact_statement'] in passage,'statement text');ck(sha(it['exact_statement'].encode())==it['statement_sha256'],'statement hash')
  else:ck(sha(passage.encode())==it['range_sha256'],'read range')
 counts['author_'+name]=len(items)
items=read(OLD/'input-snapshots.json')
for it in items:filecheck(it['snapshot'],it['sha256'],it['bytes'])
counts['author_input_snapshots']=len(items)
items=read(OLD/'literature/manifest.json')
for it in items:
 filecheck(it['file'],it['sha256']);filecheck(it['text_file'],it['text_sha256'])
counts['author_primary_retrievals']=len(items)
items=read(OLD/'primary-statement-contracts.json')
for it in items:
 text=(FROZEN/it['text_file']).read_text()[it['start_char']:it['end_char']];ck(text==it['exact_statement'],'primary passage');ck(sha(text.encode())==it['statement_sha256'],'primary hash')
counts['author_primary_contracts']=len(items)
items=read(OLD/'literature/latest-upstream-comparison.json')['files']
for it in items:
 b=filecheck(it['file'],it['sha256']);ck(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==it['git_blob'],'latest comparison blob')
counts['author_latest_comparison_blobs']=len(items)
items=read(OLD/'artifact-manifest.json')['files']
for it in items:filecheck(it['path'],it['sha256'],it['bytes'])
counts['author_sealed_artifacts']=len(items)
for name in ['source-contracts.json','read-ranges.json']:
 items=json.loads((SRC/name).read_text())
 for it in items:
  lines=(FROZEN/it['local']).read_text().splitlines(keepends=True);text=''.join(lines[it['start_line']-1:it['end_line']]);ck(it['git_blob']==by_local[it['local']]['git_blob'],'R2 source')
  if 'exact_statement' in it:ck(it['exact_statement'] in text,'R2 statement');ck(sha(it['exact_statement'].encode())==it['statement_sha256'],'R2 statement hash')
  else:ck(sha(text.encode())==it['range_sha256'],'R2 read range')
 counts['r2_'+name]=len(items)
exp=BASE/'frontier/experiments/i17_six_point_ramsey_r2'
for name in ['diagnostics.json','series-diagnostics.json']:
 live=(exp/'author-reproduction'/name).read_bytes();source=(FROZEN/'frontier/experiments/i17_fresh_discovery'/name).read_bytes();ck(live==source,'author reproduction '+name)
for it in json.loads((exp/'vendor/manifest.json').read_text()):ck(sha((exp/'vendor'/it['file']).read_bytes())==it['sha256'],'vendor '+it['file'])
for name in ['independent-checks.json','factorized-check.json']:ck(json.loads((exp/name).read_text())['status']=='PASS','independent '+name)
result={'status':'FAIL' if errors else 'PASS','counts':counts,'errors':errors,'live_inputs_changed_since_r2_freeze':live_changes,'candidate_sha256':sha(report.read_bytes()),'scope':'All frozen bytes, source identities and reproduced diagnostics verified; source truth and mathematical deduction are separate.'}
(SRC/'input-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));raise SystemExit(bool(errors))
