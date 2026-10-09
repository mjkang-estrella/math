"""I32 integrity verifier. --seal records the current deliverables; never run it to hide drift."""
from pathlib import Path
import json,hashlib,sys,datetime,subprocess
from urllib.parse import unquote
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i32_geometric_relativity_discovery'
E=R/'frontier/experiments/i32_geometric_relativity_discovery'
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
REPORT=R/'frontier/iterations/i32-geometric-relativity-discovery.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
SEAL=S/'artifact-seal.json'
EXCLUDE={SEAL,E/'verification.json',E/'live-drift.json'}
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def artifacts():return sorted({REPORT}|{p for root in (S,E) for p in root.rglob('*') if p.is_file() and p not in EXCLUDE})
def relative(p):return str(p.relative_to(R))
if '--seal' in sys.argv:
    SEAL.write_text(json.dumps({'pin':PIN,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':[{'path':relative(p),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in artifacts()]},indent=2)+'\n')

errors=[];counts={}
def check(ok,msg):
    if not ok:errors.append(msg)
seal=read(SEAL);check(seal['pin']==PIN,'seal pin')
for e in seal['files']:
    p=R/e['path'];check(p.exists() and sha(p.read_bytes())==e['sha256'],'sealed artifact '+e['path'])
check({e['path'] for e in seal['files']}=={relative(p) for p in artifacts()},'artifact file set changed')
counts['sealed_artifacts']=len(seal['files'])

drift=[]
for e in read(S/'input-manifest.json'):
    b=(R/e['frozen']).read_bytes();check(sha(b)==e['sha256'],'frozen input '+e['path'])
    p=R/e['path'];live=sha(p.read_bytes()) if p.exists() else None
    if live!=e['sha256']:drift.append({'path':e['path'],'frozen_sha256':e['sha256'],'live_sha256':live,'classification':'live shared-input drift; frozen input remains authoritative for this report'})
counts['frozen_inputs']=len(read(S/'input-manifest.json'))
for e in read(S/'dependency-manifest.json'):
    check(sha((R/e['path']).read_bytes())==e['sha256'],'read-only dependency '+e['path'])

tree=read(R/'sources/preprints-tree.json');check(tree['truncated'] is False,'complete tree flag')
tree_blobs={e['path']:e['sha'] for e in tree['tree'] if e['type']=='blob'}
corpus=read(C.parent/'corpus-manifest.json');check(corpus['pin']==PIN,'corpus pin')
check(len(corpus['files'])==9340,'9340 manifest files')
for e in corpus['files']:
    p=C/e['path']
    if not p.exists():errors.append('missing corpus '+e['path']);continue
    b=p.read_bytes()
    check(sha(b)==e['sha256'],'corpus sha '+e['path'])
    check(blob(b)==e['git_blob']==tree_blobs.get(e['path']),'corpus Git/tree '+e['path'])
    check(unquote(e['url'])=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path'],'pinned raw URL '+e['path'])
counts['reused_corpus_files']=len(corpus['files'])
check(len({e['path'].split('/')[1] for e in corpus['files']})==749,'749 manuscript directories')

source=read(S/'source-manifest.json')
for e in source['files']:
    b=(R/e['local_path']).read_bytes()
    check(sha(b)==e['sha256'] and blob(b)==e['git_blob'],'selected source '+e['path'])
counts['selected_pinned_sources']=len(source['files'])
for e in read(S/'contracts.json'):
    p=C/e['path'];text=p.read_text()
    check(sha(p.read_bytes())==e['sha256'],'contract hash '+e['id'])
    for label in e['labels']:check('\\label{'+label+'}' in text,'contract label '+label)
counts['contracts']=len(read(S/'contracts.json'))

frozen={e['path']:R/e['frozen'] for e in read(S/'input-manifest.json')}
passages=read(S/'read-passages.json')
for e in passages:
    p=frozen.get(e['path'],R/e['path']);b=p.read_bytes()
    check(sha(b)==e['sha256'],'passage file '+e['path'])
    lines=p.read_text().splitlines(keepends=True);chunk=''.join(lines[e['first']-1:e['last']])
    check(sha(chunk.encode())==e['passage_sha256'],'passage range '+e['path']+':'+str(e['first']))
counts['logged_passages']=len(passages)

retrievals=read(S/'literature/manifest.json')+[read(S/'literature/charged-collars-fetch.json')]
failed=[]
for e in retrievals:
    if 'path' in e:check(sha((R/e['path']).read_bytes())==e['sha256'],'retrieval '+e['url'])
    if 'text_path' in e:check(sha((R/e['text_path']).read_bytes())==e['text_sha256'],'extraction '+e['url'])
    if e.get('status')!=200:failed.append({'url':e['url'],'status':e.get('status'),'error':e.get('error')})
counts['primary_responses']=len(retrievals)
counts['retained_failed_responses']=len(failed)

run=subprocess.run([sys.executable,str(E/'diagnostics.py')],cwd=R,capture_output=True,text=True)
check(run.returncode==0,'diagnostics execution: '+run.stderr)
if run.returncode==0:check(json.loads(run.stdout)['status']=='PASS','diagnostic status')
# Recheck diagnostics after its deterministic reproduction.
de=next(e for e in seal['files'] if e['path']==relative(E/'diagnostics.json'))
check(sha((E/'diagnostics.json').read_bytes())==de['sha256'],'diagnostics reproducibility')
counts['rosen_exact_jet_checks']=read(E/'diagnostics.json')['rosen_exact_jet_checks']

(E/'live-drift.json').write_text(json.dumps({'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'drift':drift,'interpretation':'Live shared files are not repaired. Drift is distinct from immutable dependency/artifact integrity.'},indent=2)+'\n')
result={'status':'PASS' if not errors else 'FAIL','pin':PIN,'counts':counts,'errors':errors,'live_shared_input_drift':drift,'retained_failed_fetches':failed,'mathematical_limit':'Integrity and finite exact diagnostics do not certify the technical deduction, endpoint theorem, or significance.'}
(E/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
sys.exit(bool(errors))
