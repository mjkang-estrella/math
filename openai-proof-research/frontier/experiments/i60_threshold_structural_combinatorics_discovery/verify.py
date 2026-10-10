"""Read-only I60 replay. Never refreshes hashes, seals, ledgers, or outputs."""
from pathlib import Path
from collections import Counter
import hashlib,json,subprocess,sys,os
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i60_threshold_structural_combinatorics_discovery';E=Path(__file__).resolve().parent
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def check(ok,msg):
 if not ok:raise AssertionError(msg)
seal=read(S/'seal.json')
for row in seal['files']:check(sha((R/row['path']).read_bytes())==row['sha256'],'sealed artifact '+row['path'])
actual=sorted(str(p.relative_to(R)) for root in [S,E] for p in root.rglob('*') if p.is_file() and str(p.relative_to(R)) not in seal['excluded'])
actual.append(seal['report']);check(sorted(actual)==sorted(x['path'] for x in seal['files']),'I60 sealed inventory')
drift=[];inputs=read(S/'inputs.json')
for row in inputs:
 check(sha((R/row['frozen']).read_bytes())==row['sha256'],'frozen '+row['path'])
 now=sha((R/row['path']).read_bytes())
 if now!=row['sha256']:
  if row['mutable']:drift.append(dict(path=row['path'],frozen=row['sha256'],live=now))
  else:raise AssertionError('immutable input drift '+row['path'])
check({x['path'] for x in inputs if x['mutable']}=={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'},'four mutable ledger scope')
for row in read(S/'old-files-watch.json'):check(sha((R/row['path']).read_bytes())==row['sha256'],'old immutable '+row['path'])
tree=read(S/'inputs/sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree'] if x['type']=='blob'};corpus=read(S/'corpus-inventory.json')
check(len(tree['tree'])==13223 and not tree['truncated'],'complete tree')
check(len({x['path'].split('/')[1] for x in tree['tree']})==749,'749 manuscripts')
check(sorted(str(p.relative_to(C)) for p in C.rglob('*') if p.is_file())==sorted(x['path'] for x in corpus['files']),'complete corpus inventory')
for row in corpus['files']:
 b=(C/row['path']).read_bytes();check(sha(b)==row['sha256'] and blob(b)==lookup[row['path']]['sha']==row['git_blob'],'corpus '+row['path'])
pinned=read(S/'pinned-manifest.json')
for row in pinned:
 b=(R/row['frozen']).read_bytes();check(sha(b)==row['sha256'] and blob(b)==lookup[row['path']]['sha'],'selected '+row['path'])
for record in ['read-passages.json','source-contracts.json']:
 for row in read(S/record):
  lines=(R/row['file']).read_text().splitlines(keepends=True);b=''.join(lines[row['start']-1:row['end']]).encode();check(sha(b)==row['sha256'],'passage '+row['file'])
responses=read(S/'literature/responses.json')
for row in responses:
 if 'file' in row:check(sha((R/row['file']).read_bytes())==row['sha256'],'primary '+row['name'])
 if 'text' in row:check(sha((R/row['text']).read_bytes())==row['text_sha256'],'primary text '+row['name'])
for row in read(S/'fresh-pinned-responses.json'):
 check(row.get('matches_selected') and row.get('status')==200,'fresh pinned failure')
 b=(R/row['file']).read_bytes();check(sha(b)==row['sha256'] and blob(b)==lookup[row['path']]['sha'],'fresh pin '+row['path'])
# Reproduce search multisets against the frozen list, never a growing prior-report glob.
terms=['slice','threshold','convexity','influence','Hall','root','matching','prophet'];hits=[]
for row in inputs:
 if '/iterations/i' not in row['path']:continue
 for i,line in enumerate((R/row['frozen']).read_text().splitlines(),1):
  for term in terms:
   if term.lower() in line.lower():hits.append([row['path'],i,term,line])
expected=read(S/'prior-screen-lines.json');check(Counter(tuple(x) for x in hits)==Counter(tuple(x) for x in expected),'prior line multiset')
cs=read(S/'corpus-search.json');p=subprocess.run(cs['command'],cwd=R,capture_output=True,text=True);check(p.returncode==cs['returncode'] and Counter(p.stdout.splitlines())==Counter(cs['lines']),'corpus line multiset')
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');p=subprocess.run([sys.executable,str(E/'diagnostics.py')],cwd=R,env=env,capture_output=True,text=True)
check(p.returncode==0,'diagnostics exit: '+p.stderr);result=json.loads(p.stdout);check(result==read(E/'exact-results.json'),'exact diagnostics replay')
print(json.dumps(dict(status='PASS',sealed_artifacts=len(seal['files']),frozen_inputs=len(inputs),watched_old_files=len(read(S/'old-files-watch.json')),pinned_files=len(pinned),corpus_files=len(corpus['files']),passages=len(read(S/'read-passages.json')),source_contracts=len(read(S/'source-contracts.json')),primary_requests=len(responses),fresh_pinned_responses=len(read(S/'fresh-pinned-responses.json')),exact_assertions=result['assertions'],mutable_ledger_drift=drift,scope='Evidence and finite identities only; not independent analytic review or novelty certification'),indent=2))
