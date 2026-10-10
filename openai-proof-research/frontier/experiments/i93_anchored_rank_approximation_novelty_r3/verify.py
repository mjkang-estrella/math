#!/usr/bin/env python3
"""Offline READ-ONLY evidence replay. No fetch/write/repair/reseal.
--preseal runs all content checks before the one final seal exists.
Hash and finite-diagnostic PASS is neither original-proof PASS nor certification.
"""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
SRC='frontier/sources/i93_anchored_rank_approximation_novelty_r3'
EXP='frontier/experiments/i93_anchored_rank_approximation_novelty_r3'
REPORT='frontier/reviews/i93-anchored-rank-approximation-novelty-r3.md'
SEAL=SRC+'/seal.json'
OLD='frontier/sources/i90_anchored_rank_approximation'
OLD_HASH='89f356914c26239322fdd3f1bb42dd9a124be0d6867ce65d02e3bf1276813438'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def read(p):return (ROOT/p).read_bytes()
def load(p):return json.loads(read(p))
def sha(b):return hashlib.sha256(b).hexdigest()
def need(ok,msg):
 if not ok:raise AssertionError(msg)
def inventory():
 paths={REPORT}
 for d in [SRC,EXP]:
  for p in (ROOT/d).rglob('*'):
   need(not p.is_symlink(),'Owned symlink '+str(p))
   if p.is_file():paths.add(p.relative_to(ROOT).as_posix())
 paths.discard(SEAL);return sorted(paths)
def main():
 preseal=sys.argv[1:]==['--preseal']
 need(not sys.argv[1:] or preseal,'Only --preseal is supported')
 own=inventory()
 if preseal:
  need(not (ROOT/SEAL).exists(),'No preseal runs after seal');print('PRESEAL: no final seal yet',flush=True)
 else:
  s=load(SEAL)
  need(s['pin']==PIN and s['owned_report']==REPORT and s['owned_directories']==[SRC,EXP] and s['self_exclusion']==SEAL,'Owned scope')
  rows=s['files'];need([r['path'] for r in rows]==own,'Exact sorted owned inventory')
  for r in rows:
   b=read(r['path']);need(len(b)==r['bytes'] and sha(b)==r['sha256'],'Owned bytes '+r['path'])
 need(sha(read(OLD+'/seal.json'))==OLD_HASH,'I90 seal changed')
 refs=load(SRC+'/immutable-references.json');need(len({r['path'] for r in refs})==len(refs),'Duplicate immutable refs')
 for r in refs:
  need(not r['path'].startswith(('frontier/sources/i91_','frontier/experiments/i91_','frontier/sources/i92_','frontier/experiments/i92_')),'Forbidden active dependency')
  b=read(r['path']);need(len(b)==r['bytes'] and sha(b)==r['sha256'],'Immutable reference '+r['path'])
 inputs=load(SRC+'/inputs.json');need({r['original'] for r in inputs if r['may_drift']}==DRIFT,'Exact ledger drift allowlist')
 drift=[]
 for r in inputs:
  need(sha(read(r['snapshot']))==r['sha256'],'Frozen snapshot '+r['snapshot'])
  if sha(read(r['original']))!=r['sha256']:
   need(r['may_drift'] and r['original'] in DRIFT,'Immutable input changed');drift.append(r['original'])
 need(read(SRC+'/original-i90-report.md')==read('frontier/iterations/i90-anchored-rank-approximation.md'),'I90 original report preservation')
 need(read(SRC+'/original-i90-brief.txt').decode()==load('frontier/iterations/iteration90-anchored-rank-approximation-task.json')['brief'],'I90 original brief preservation')
 need(read(SRC+'/finalized-i90-parent-response.json')==read('frontier/experiments/i90-parent-verification.json'),'Finalized parent response preservation')
 brief=read(SRC+'/original-i93-brief.txt').decode()
 need('I93' in brief and 'FULL I90 REPORT:' in brief and 'FINALIZED PARENT REPLAY / RESPONSE:' in brief,'Complete supplied brief sections')
 report=read(SRC+'/original-i90-report.md').decode()
 need(report.strip() in brief,'Full I90 report in supplied brief')
 print('Owned/frozen inputs, preserved brief/report/parent response and immutable references PASS',flush=True)
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
 # Unchanged inherited verifier validates I90/I88 domains, ALL 10373 originals,
 # I79 provenance, inherited 776 extraction hashes, 3 I90 queries and 6 primary PDFs.
 inherited=subprocess.run([sys.executable,'-B','frontier/experiments/i90_anchored_rank_approximation/verify.py'],cwd=ROOT,env=env,capture_output=True)
 need(inherited.returncode==0,'Inherited I90 evidence replay failed: '+inherited.stdout.decode()+inherited.stderr.decode())
 out=inherited.stdout.decode();need('"status": "EVIDENCE PASS"' in out and '"pinned_blobs": 10373' in out and '"primary_pdf_replays": 6' in out,'Inherited output scope')
 print('Unchanged I90 evidence replay PASS: all 10373 original blobs, 776 inherited text hashes, 3 searches, 6 primary PDF replays; NOT A PROOF',flush=True)
 tree=load('sources/preprints-tree.json');need(not tree['truncated'] and len(tree['tree'])==13223,'Full tree')
 domain=load('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json')
 need(len(domain)==len({r['path'] for r in domain})==10373 and len({r['path'].split('/')[1] for r in domain})==749,'Domain counts')
 need({r['path'] for r in domain}=={r['path'] for r in tree['tree'] if r['type']=='blob'},'Tree/domain identity')
 i79={r['path']:r for r in load('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')}
 need(all(all(r[k]==i79[r['path']][k] for k in ['path','local','kind','sha256']) for r in domain),'I79 augmentation identity')
 got=sorted(p.relative_to(ROOT).as_posix() for p in (ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus').rglob('*') if p.is_file())
 need(got==read(SRC+'/i14-rg-inventory.txt').decode().splitlines() and len(got)==9340,'Exact rg corpus inventory')
 fam=load(SRC+'/families.json');selected=[dict(r,alias=next(a for a,f in fam.items() if f==r['path'].split('/')[1])) for r in domain if r['path'].split('/')[1] in fam.values()]
 need(selected==load(SRC+'/selected-inventory.json') and len(selected)==43,'All four-family representations')
 reads=load(SRC+'/read-manifest.json')
 for r in reads:
  b=read(r['path']);ls=b.decode().splitlines(keepends=True)
  need(sha(b)==r['sha256'] and 1<=r['start']<=r['end']<=len(ls),'Read source '+r['path'])
  need(sha(''.join(ls[r['start']-1:r['end']]).encode())==r['passage_sha256'],'Read passage '+r['path'])
 states=[]
 for q in load(SRC+'/queries.json'):
  need(q['flags']=='IGNORECASE','Regex flags');states.append([q,re.compile(q['pattern'],re.I),hashlib.sha256(),0,{}])
 for i,r in enumerate(domain,1):
  for n,line in enumerate((ROOT/r['local']).read_text(encoding='utf-8',errors='replace').splitlines(),1):
   for z in states:
    q,pat,h,_,families=z
    if pat.search(line):
     row=dict(path=r['path'],local=r['local'],line=n,text=line);h.update((json.dumps(row,ensure_ascii=False)+'\n').encode());z[3]+=1;family=r['path'].split('/')[1];families[family]=families.get(family,0)+1
  if i%3000==0:print('I93 full-domain search replay:',i,flush=True)
 for q,pat,h,count,families in states:
  need(count==q['records'] and len(families)==q['manuscripts'],'Query counts '+q['name'])
  need(h.hexdigest()==sha(read(SRC+'/search-'+q['name']+'.jsonl')),'Ordered search multiset '+q['name'])
 summary=[dict(name=q['name'],families=[list(x) for x in sorted(families.items(),key=lambda x:(-x[1],x[0]))]) for q,pat,h,count,families in states]
 need(summary==load(SRC+'/search-summary.json'),'Exact search family inventory')
 web=load(SRC+'/external/web-search-index.json');need([r['round'] for r in web]==[1,2,3,4],'Four bounded web searches')
 for r in web:need(sha(read(r['response_path']))==r['response_sha256'],'Bounded search response')
 diag=subprocess.run([sys.executable,'-B',str(ROOT/EXP/'diagnostics.py')],cwd=ROOT,env=env,capture_output=True,check=True)
 need(diag.stdout==read(EXP+'/diagnostics.json'),'Independent finite diagnostics mismatch')
 pdfs=responses=0
 for p in sorted((ROOT/SRC/'external').glob('*.response.json')):
  r=json.loads(p.read_bytes());need(r.get('status')==200 and 'error' not in r,'Primary request '+str(p))
  b=read(SRC+'/external/'+r['name']);need(len(b)==r['bytes'] and sha(b)==r['sha256'],'Primary bytes '+r['name']);responses+=1
  if 'text' in r:
   need(r['extraction_returncode']==0,'Extraction return code')
   path=SRC+'/external/'+r['text'];need(sha(read(path))==r['text_sha256'],'Saved text hash')
   result=subprocess.run(['pdftotext','-layout',str(ROOT/SRC/'external'/r['name']),'-'],capture_output=True,check=True)
   need(result.stdout==read(path),'New primary PDF replay '+r['name']);pdfs+=1
 for r in load(SRC+'/primary-evidence.json'):need(sha(read(r['path']))==r['sha256'],'Primary comparison body '+r['path'])
 need(pdfs==2 and responses==4,'New primary inventory')
 scope=load(SRC+'/evidence-scope.json');need(scope['selected_blobs']==len(selected) and scope['read_records']==len(reads) and scope['immutable_reference_count']==len(refs),'Evidence scope counts')
 print(json.dumps(dict(status='PRESEAL CHECKS PASS; NOT SEALED' if preseal else 'EVIDENCE PASS',owned_files=len(own),immutable_references=len(refs),read_records=len(reads),selected_blobs=len(selected),pinned_original_blobs=10373,manuscripts=749,inherited_extraction_hashes=776,i93_search_multisets=[z[3] for z in states],inherited_i90_search_multisets=[84,554,8],new_primary_responses=responses,new_primary_pdf_replays=pdfs,inherited_primary_pdf_replays=6,all_corpus_pdf_reextraction=False,allowed_ledger_drift=drift,diagnostics=json.loads(diag.stdout)['counts'],original_proof_verdict='NOT GIVEN BY I93; CONDITIONED ON I92',contribution_verdict='TECHNICAL; WRITTEN REDUCTION IN REPORT, NOT ESTABLISHED BY HASHES',count_increment=0),indent=2))
if __name__=='__main__':
 try:main()
 except Exception as e:print('EVIDENCE FAIL:',type(e).__name__+':',str(e),file=sys.stderr);sys.exit(1)
