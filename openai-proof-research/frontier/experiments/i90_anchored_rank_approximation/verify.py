#!/usr/bin/env python3
"""Offline READ-ONLY evidence verifier. No fetch/write/repair/reseal.
Default requires the one final seal. --preseal performs all other checks before
that seal exists and explicitly does NOT return sealed evidence PASS.
"""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
SRC='frontier/sources/i90_anchored_rank_approximation'
EXP='frontier/experiments/i90_anchored_rank_approximation'
REPORT='frontier/iterations/i90-anchored-rank-approximation.md'
SEAL=SRC+'/seal.json'
OLD='frontier/sources/i88_nonlinear_banach_discovery'
OLD_SEAL_HASH='a4af4b269cef192734166e228ca2e95d6fd08ee25f03d4163a2fc4de0c9277c6'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def read(p):return (ROOT/p).read_bytes()
def load(p):return json.loads(read(p))
def sha(b):return hashlib.sha256(b).hexdigest()
def need(ok,msg):
 if not ok:raise AssertionError(msg)
def inventory(dirs,report,seal):
 paths={report}
 for d in dirs:
  for p in (ROOT/d).rglob('*'):
   need(not p.is_symlink(),'Owned symlink '+str(p))
   if p.is_file():paths.add(p.relative_to(ROOT).as_posix())
 paths.discard(seal);return paths
def check_seal(path,expected=None):
 if expected:need(sha(read(path))==expected,'Original seal hash')
 s=load(path);need(s['pin']==PIN,'Wrong pin')
 actual=inventory(s['owned_directories'],s['owned_report'],path)
 rr=s['files'];want={r['path'] for r in rr}
 need(len(want)==len(rr) and want==actual,'Owned domain mismatch '+repr(want^actual))
 for r in rr:
  b=read(r['path']);need(len(b)==r['bytes'] and sha(b)==r['sha256'],'Sealed bytes '+r['path'])
 return s

def main():
 preseal=sys.argv[1:]==['--preseal']
 need(not sys.argv[1:] or preseal,'Only --preseal is supported')
 if preseal:
  need(not (ROOT/SEAL).exists(),'Preseal mode forbidden after sealing')
  own_count=len(inventory([SRC,EXP],REPORT,SEAL));print('PRESEAL: final owned seal not yet created',flush=True)
 else:
  s=check_seal(SEAL);need(s['owned_directories']==[SRC,EXP] and s['owned_report']==REPORT and s['self_exclusion']==SEAL,'Wrong owned domain')
  own_count=len(s['files'])
 drift=[]
 for prefix in [SRC,OLD]:
  rr=load(prefix+'/inputs.json')
  need({r['original'] for r in rr if r['may_drift']}==DRIFT,'Drift allowlist')
  for r in rr:
   need(sha(read(r['snapshot']))==r['sha256'],'Frozen snapshot '+r['snapshot'])
   if sha(read(r['original']))!=r['sha256']:
    need(r['may_drift'] and r['original'] in DRIFT,'Immutable input drift '+r['original'])
    if prefix==SRC:drift.append(r['original'])
  for r in load(prefix+'/immutable-references.json'):need(sha(read(r['path']))==r['sha256'],'Immutable reference '+r['path'])
 old=check_seal(OLD+'/seal.json',OLD_SEAL_HASH)
 need(read(SRC+'/original-i88-report.md')==read('frontier/iterations/i88-nonlinear-banach-discovery.md'),'Original report preservation')
 need(read(SRC+'/original-i88-brief.txt').decode()==load('frontier/iterations/iteration88-nonlinear-banach-discovery-task.json')['brief'],'Original brief preservation')
 need(read(SRC+'/finalized-parent-response.json')==read('frontier/experiments/i88-parent-verification.json'),'Finalized response preservation')
 need(PIN in read('sources/upstream.json').decode(),'Upstream pin')
 print('Owned/input hashes, complete original brief/report/response, unchanged I88 seal PASS',flush=True)
 tree=load('sources/preprints-tree.json');need(tree['truncated'] is False and len(tree['tree'])==13223,'Tree incomplete')
 blobs={r['path']:r for r in tree['tree'] if r['type']=='blob'}
 domain=load(OLD+'/search-domain.json');by={r['path']:r for r in domain}
 need(len(blobs)==len(domain)==len(by)==10373 and set(blobs)==set(by),'Original-position domain')
 need(len({p.split('/')[1] for p in by})==749,'Manuscript count')
 i79={r['path']:r for r in load('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')}
 need(set(i79)==set(by),'I79 domain')
 reqs=[json.loads(l) for l in read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').splitlines()]
 outside={r['path']:r for r in reqs};need(len(reqs)==len(outside)==1033,'Outside requests')
 corpus=extracted=0
 for index,r in enumerate(domain,1):
  p=r['path'];need(all(r[k]==i79[p][k] for k in ['path','local','kind','sha256']),'I79 map mismatch '+p)
  b=read(r['original_local']);git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  need(git==r['git_sha']==blobs[p]['sha'] and sha(b)==r['original_sha256'],'Pinned original '+p)
  body=b if r['local']==r['original_local'] else read(r['local'])
  need(sha(body)==r['sha256'],'Search body '+p)
  if p in outside:
   q=outside[p];need(q['status']==200 and q['git_match'] and PIN in q['url'],'Outside provenance '+p)
   need(q['local']==r['original_local'] and q['sha256']==r['original_sha256'] and q['sha']==git,'Outside mapping '+p)
   if 'extraction' in q:
    e=q['extraction'];need(e['code']==0 and e['path']==r['local'] and e['sha256']==r['sha256'],'Extraction mapping '+p);extracted+=1
  else:
   need(r['kind']=='corpus','Unmapped original '+p);corpus+=1
  if index%2000==0:print('Verified original/search bodies:',index,flush=True)
 need(corpus==9340 and extracted==776,'Body totals')
 got=sorted(p.relative_to(ROOT).as_posix() for p in (ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus').rglob('*') if p.is_file())
 need(got==read(SRC+'/i14-rg-inventory.txt').decode().splitlines(),'rg corpus inventory')
 need(set(got)=={r['original_local'] for r in domain if r['kind']=='corpus'},'Corpus mapped inventory')
 fam=load(SRC+'/families.json')
 want=[dict(r,alias=next(a for a,f in fam.items() if f==r['path'].split('/')[1])) for r in domain if r['path'].split('/')[1] in fam.values()]
 need(want==load(SRC+'/selected-inventory.json'),'Companion inventory')
 for r in load(SRC+'/read-manifest.json'):
  b=read(r['path']);ls=b.decode().splitlines(keepends=True)
  need(sha(b)==r['sha256'] and 1<=r['start']<=r['end']<=len(ls),'Read source '+r['path'])
  need(sha(''.join(ls[r['start']-1:r['end']]).encode())==r['passage_sha256'],'Read passage '+r['path'])
 print('All 10373 blob positions, I79 provenance and read passages PASS',flush=True)
 states=[]
 for q in load(SRC+'/queries.json'):
  need(q['flags']=='IGNORECASE','Regex flags');states.append([q,re.compile(q['pattern'],re.I),hashlib.sha256(),0,set()])
 for index,r in enumerate(domain,1):
  for number,line in enumerate((ROOT/r['local']).read_text(encoding='utf-8',errors='replace').splitlines(),1):
   for state in states:
    q,pat,h,_,families=state
    if pat.search(line):
     row=dict(path=r['path'],local=r['local'],line=number,text=line);h.update((json.dumps(row,ensure_ascii=False)+'\n').encode());state[3]+=1;families.add(r['path'].split('/')[1])
  if index%2000==0:print('Replayed full-domain queries:',index,flush=True)
 for q,pat,h,count,families in states:
  need(count==q['records'] and len(families)==q['manuscripts'],'Search count '+q['name'])
  need(h.hexdigest()==sha(read(SRC+'/search-'+q['name']+'.jsonl')),'Ordered search multiset '+q['name'])
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
 result=subprocess.run([sys.executable,'-B',str(ROOT/EXP/'diagnostics.py')],cwd=ROOT,env=env,capture_output=True,check=True)
 need(result.stdout==read(EXP+'/diagnostics.json'),'Finite diagnostics differ')
 pdfs=responses=0
 for p in sorted((ROOT/SRC/'external').glob('*.response.json')):
  r=json.loads(p.read_bytes());need(r.get('status')==200,'Primary response '+str(p))
  b=read(SRC+'/external/'+r['name']);need(len(b)==r['bytes'] and sha(b)==r['sha256'],'Primary bytes '+r['name']);responses+=1
  if 'text' in r:
   need(r['extraction_returncode']==0 and sha(read(r['text']))==r['text_sha256'],'Primary saved text '+r['name'])
   out=subprocess.run(['pdftotext','-layout',str(ROOT/SRC/'external'/r['name']),'-'],capture_output=True,check=True)
   need(out.stdout==read(r['text']),'Primary PDF re-extraction '+r['name']);pdfs+=1
 out=subprocess.run(['pdftotext','-layout',str(ROOT/OLD/'external/local-reflexivity.pdf'),'-'],capture_output=True,check=True)
 need(out.stdout==read(OLD+'/external/local-reflexivity.txt'),'Inherited local-reflexivity PDF re-extraction');pdfs+=1
 print(json.dumps(dict(status='PRESEAL CHECKS PASS; NOT SEALED' if preseal else 'EVIDENCE PASS',owned_files=own_count,i88_owned_files=len(old['files']),pinned_blobs=10373,manuscripts=749,corpus_files=corpus,inherited_extraction_hashes=extracted,search_multisets=[s[3] for s in states],primary_responses=responses,primary_pdf_replays=pdfs,read_records=len(load(SRC+'/read-manifest.json')),allowed_ledger_drift=drift,diagnostics='FINITE STRESS TESTS ONLY',original_i88_proof_verdict='WRITTEN IN REPORT; NOT ESTABLISHED BY VERIFIER',q90_proof_verdict='AUTHOR PROOF; INDEPENDENT REVIEW NOT PERFORMED BY VERIFIER',contribution_verdict='PARENT DECISION; NO ACCEPTANCE OR COUNT INCREMENT'),indent=2))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print('EVIDENCE FAIL:',type(e).__name__+':',str(e),file=sys.stderr);sys.exit(1)
