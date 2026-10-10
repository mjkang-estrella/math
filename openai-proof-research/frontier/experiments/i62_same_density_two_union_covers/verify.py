"""Read-only I62 replay. Does not refresh any input, seal, or output file."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess,sys,os
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i62_same_density_two_union_covers';E=Path(__file__).resolve().parent;C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def ck(ok,msg):
 if not ok:raise AssertionError(msg)
seal=read(S/'seal.json')
for row in seal['files']:ck(sha((R/row['path']).read_bytes())==row['sha256'],'seal '+row['path'])
actual=[str(p.relative_to(R)) for root in [S,E] for p in root.rglob('*') if p.is_file() and str(p.relative_to(R)) not in seal['excluded']]+[seal['report']]
ck(sorted(actual)==sorted(x['path'] for x in seal['files']),'owned-file inventory')
inputs=read(S/'inputs.json');drift=[]
for row in inputs:
 ck(sha((R/row['frozen']).read_bytes())==row['sha256'],'frozen '+row['path'])
 live=sha((R/row['path']).read_bytes())
 if live!=row['sha256']:
  ck(row['mutable'],'immutable changed '+row['path']);drift.append(dict(path=row['path'],frozen=row['sha256'],live=live))
ck({x['path'] for x in inputs if x['mutable']}=={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'},'four mutable ledgers')
for row in read(S/'old-watch.json'):ck(sha((R/row['path']).read_bytes())==row['sha256'],'old immutable '+row['path'])
tree=read(S/'inputs/sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree'] if x['type']=='blob'}
ck(len(tree['tree'])==13223 and not tree['truncated'],'complete tree');ck(len({x['path'].split('/')[1] for x in tree['tree']})==749,'manuscript count')
inv=read(S/'corpus-inventory.json');ck(sorted(str(p.relative_to(C)) for p in C.rglob('*') if p.is_file())==sorted(x['path'] for x in inv),'full ignored corpus inventory')
for row in inv:
 b=(C/row['path']).read_bytes();ck(sha(b)==row['sha256'] and blob(b)==lookup[row['path']]['sha']==row['git_blob'],'corpus '+row['path'])
for row in read(S/'pinned-manifest.json'):
 b=(R/row['file']).read_bytes();ck(sha(b)==row['sha256'] and blob(b)==lookup[row['path']]['sha']==row['git_blob'],'selected pin '+row['path'])
for name in ['read-passages.json','source-contracts.json']:
 for row in read(S/name):
  lines=(R/row['file']).read_text().splitlines(keepends=True);b=''.join(lines[row['start']-1:row['end']]).encode();ck(sha(b)==row['sha256'],'passage '+row['label'])
for row in read(S/'literature/responses.json'):
 if 'file' in row:ck(sha((R/row['file']).read_bytes())==row['sha256'],'primary '+row['name'])
 if 'text' in row:ck(sha((R/row['text']).read_bytes())==row['text_sha256'],'primary conversion '+row['name'])
for row in read(S/'fresh-pinned.json'):
 ck(row['status']==200 and row['matches_selected'],'fresh response');b=(R/row['file']).read_bytes();ck(sha(b)==row['sha256'] and blob(b)==lookup[row['path']]['sha'],'fresh pin')
prior=read(S/'prior-search.json');hits=[]
for row in inputs:
 if '/iterations/i' not in row['path']:continue
 for i,line in enumerate((R/row['frozen']).read_text().splitlines(),1):
  for term in prior['terms']:
   if re.search(term,line,re.I):hits.append([row['path'],i,term,line])
ck(Counter(tuple(x) for x in hits)==Counter(tuple(x) for x in prior['lines']),'frozen prior line multiset')
for name in ['corpus-search.json','companion-search.json']:
 record=read(S/name);p=subprocess.run(record['command'],cwd=R,capture_output=True,text=True)
 ck(p.returncode==record['returncode'] and Counter(p.stdout.splitlines())==Counter(record['lines']),'fixed corpus multiset '+name)
old=read(S/'i60-readonly-replay.json');ck(old['exit_code']==0 and json.loads(old['stdout'])['status']=='PASS','preserved I60 read-only replay')
results=[]
for script,expected in [('diagnostics.py','exact-results.json'),('construction_checks.py','construction-results.json')]:
 p=subprocess.run([sys.executable,str(E/script)],cwd=R,capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
 ck(p.returncode==0,'diagnostic failure '+p.stderr);result=json.loads(p.stdout);ck(result==read(E/expected),'exact replay '+script);results.append(dict(script=script,assertions=result['assertions']))
print(json.dumps(dict(status='PASS',sealed_files=len(seal['files']),frozen_inputs=len(inputs),old_watches=len(read(S/'old-watch.json')),corpus_files=len(inv),pinned_files=len(read(S/'pinned-manifest.json')),passages=len(read(S/'read-passages.json')),source_contracts=len(read(S/'source-contracts.json')),primary_requests=len(read(S/'literature/responses.json')),fresh_pins=len(read(S/'fresh-pinned.json')),diagnostics=results,exact_assertions=sum(x['assertions'] for x in results),mutable_ledger_drift=drift,scope='Evidence and exact finite computations; not independent analytic or significance certification'),indent=2))
