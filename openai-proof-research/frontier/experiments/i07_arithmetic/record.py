"""Record retained source identities, exact label windows, and artifact hashes."""
import json,hashlib,re
from pathlib import Path
root=Path(__file__).resolve().parents[3]; out=root/'frontier/sources/i07_arithmetic'; exp=root/'frontier/experiments/i07_arithmetic'
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,value): (out/name).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')
manifest=json.loads((out/'retrieval-manifest.json').read_text()); tree={e['path']:e for e in json.loads((root/'sources/preprints-tree.json').read_text())['tree']}
checks=[]
for row in manifest['files']:
 data=(root/row['local']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert sha(data)==row['sha256'] and blob==row['git_blob']==tree[row['path']]['sha']
 assert f"/{manifest['pin']}/" in row['url']
 checks.append(row['path'])
labels=['thm:type-II','det:cauchy-square','lem:marked-coefficient-transfer','eq:type-ii-cauchy-square','thm:two-sided','cor:centered-core','prop:graph-transfer','prop:ideal-family','cor:shared-collision','cor:bilinear-multiplier','lem:divisor-model','cor:low-main-term','cor:sparse-bound','cor:long-prime-saving','cor:constant-high','cor:transference-pairing','thm:elliott','thm:q-affine','eq:distribution-characters','prop:large-prime-tail','prop:cyclotomic-central','app:quartic-extension','lem:balanced-factorization','prop:parameter-certificate','thm:affine-counting','thm:main','prop:dispersion','sh:sign','sh:core','spl:smooth-estimate','spl:field-bounds']
locators=[]
for row in manifest['files']:
 lines=(root/row['local']).read_text().splitlines(keepends=True)
 for i,line in enumerate(lines):
  for label in labels:
   if '\\label{'+label+'}' in line:
    start=max(0,i-12);end=min(len(lines),i+72)
    excerpt=''.join(lines[start:end])
    locators.append({'source':row['local'],'label':label,'label_line':i+1,'start_line':start+1,'end_line':end,'sha256':sha(excerpt.encode()),'excerpt':excerpt})
write('source-locators.json',locators)
inputs=[]
for row in json.loads((out/'input-snapshot.json').read_text()):
 now=sha((root/row['path']).read_bytes());inputs.append({'path':row['path'],'snapshot_sha256':row['sha256'],'current_sha256':now,'unchanged':now==row['sha256']})
lit_checks=[]
for row in json.loads((out/'literature-manifest.json').read_text())['files']:
 if 'sha256' in row:
  p=out/'literature'/row['name'];assert sha(p.read_bytes())==row['sha256'];lit_checks.append(row['name'])
write('validation.json',{'pinned_files_checked':len(checks),'pinned_sha256_and_git_blob_failures':0,'source_windows':len(locators),'literature_files_checked':lit_checks,'input_checks':inputs,'scope':'Source identity and exact algebra are checked. CM and I_z remain unproved; no substantial finding claimed.'})
report=root/'frontier/iterations/i07-arithmetic.md'
artifacts=[report]+sorted(p for p in out.rglob('*') if p.is_file() and p.name!='artifact-hashes.json')+sorted(p for p in exp.rglob('*') if p.is_file())
write('artifact-hashes.json',[{'path':str(p.relative_to(root)),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in artifacts])
print(json.dumps({'pinned_files':len(checks),'source_windows':len(locators),'artifacts':len(artifacts),'changed_inputs':[r['path'] for r in inputs if not r['unchanged']],'failures':0}))
