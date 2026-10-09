from pathlib import Path
import json,hashlib,sys
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i20_pde_kinetic_discovery'
E=ROOT/'frontier/experiments/i20_pde_kinetic_discovery'
REPORT=ROOT/'frontier/iterations/i20-pde-kinetic-discovery.md'
SEAL=S/'artifact-seal.json';RESULT=E/'verification.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
files=lambda: sorted({p for d in (S,E) for p in d.rglob('*') if p.is_file() and p not in (SEAL,RESULT)}|{REPORT})
if '--seal' in sys.argv:
 SEAL.write_text(json.dumps({'scope':'Only I20 report and assigned source/experiment trees; excludes this seal and derived verification.json','files':[{'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files()]},indent=2)+'\n')
errors=[];drift=[];counts={}
def check(ok,msg):
 if not ok:errors.append(msg)
inp=json.loads((S/'input-manifest.json').read_text())['files']
for r in inp:
 p=S/'inputs'/r['path'];check(sha(p.read_bytes())==r['sha256'],'frozen input '+r['path'])
 live=ROOT/r['path']
 if not live.exists() or sha(live.read_bytes())!=r['sha256']:drift.append({'path':r['path'],'frozen_sha256':r['sha256'],'live_sha256':sha(live.read_bytes()) if live.exists() else None})
counts['frozen_inputs']=len(inp)
tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());check(not tree.get('truncated',False),'truncated tree')
blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
pin=json.loads((S/'pinned-manifest.json').read_text())
for r in pin['files']:
 b=(S/'corpus'/r['path']).read_bytes()
 check(sha(b)==r['sha256'],'source SHA256 '+r['path'])
 check(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']==blobs.get(r['path']),'source blob '+r['path'])
 check(r['url']=='https://raw.githubusercontent.com/openai/math/'+pin['pin']+'/'+r['path'],'source pinned URL '+r['path'])
counts['pinned_files']=len(pin['files'])
for r in json.loads((S/'reading-locators.json').read_text()):
 lines=(S/'corpus'/r['path']).read_text().splitlines()
 check('\\label{'+r['label']+'}' in lines[r['line']-1],'reading locator '+r['label'])
 check('\n'.join(lines[r['excerpt_start']-1:r['excerpt_end']])==r['excerpt'],'reading excerpt '+r['label'])
contracts=json.loads((S/'statement-contracts.json').read_text())['contracts']
for r in contracts:
 text=(S/'corpus'/r['path']).read_text();check(r['text'] in text,'statement '+r['path']+' '+str(r['labels']))
counts['source_statement_contracts']=len(contracts)
lit=json.loads((S/'literature/manifest.json').read_text())
for r in lit:
 check(sha((ROOT/r['path']).read_bytes())==r['sha256'],'literature bytes '+r['id'])
 if 'text_path' in r:check(sha((ROOT/r['text_path']).read_bytes())==r['text_sha256'],'literature text '+r['id'])
counts['literature_retrievals']=len(lit);counts['literature_pdfs']=sum('text_path' in r for r in lit)
for r in json.loads((S/'literature/reading-contracts.json').read_text()):
 lines=(ROOT/r['text_path']).read_text().split('\n')
 check('\n'.join(lines[r['start_line']-1:r['end_line']])==r['text'],'literature contract '+r['id'])
sealed=json.loads(SEAL.read_text())['files']
for r in sealed:
 p=ROOT/r['path'];check(p.exists() and sha(p.read_bytes())==r['sha256'],'artifact '+r['path'])
check({r['path'] for r in sealed}=={str(p.relative_to(ROOT)) for p in files()},'artifact file set changed')
counts['sealed_artifacts']=len(sealed)
out={'status':'PASS' if not errors else 'FAIL','counts':counts,'errors':errors,'live_input_drift':drift,'drift_policy':'Frozen inputs govern this report. Live dependency drift is reported separately and does not alter the snapshot or mathematical checks.','limitation':'Integrity and finite diagnostics do not certify analytic proofs or significance.'}
RESULT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
sys.exit(bool(errors))
