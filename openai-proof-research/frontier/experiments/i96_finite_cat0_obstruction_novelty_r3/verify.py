"""Offline READ-ONLY I96 evidence verifier; no fetch/write/bytecode/repair/reseal.

--preseal validates the final candidate evidence without creating a seal.
Requires python3, rg and pdftotext. Historical verifiers are invoked unchanged.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i96_finite_cat0_obstruction_novelty_r3'
E='frontier/experiments/i96_finite_cat0_obstruction_novelty_r3'
REPORT='frontier/reviews/i96-finite-cat0-obstruction-novelty-r3.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
EX=[S+'/seal-v1.json',S+'/seal-v1.sha256']
MUTABLE=sorted(['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'])
def require(v,s):
 if not v:raise AssertionError(s)
def path(n):
 p=Path(n);require(not p.is_absolute() and '..' not in p.parts and p.as_posix()==n,'unsafe/noncanonical path '+n)
 q=R
 for part in p.parts:q=q/part;require(not q.is_symlink(),'symlink '+n)
 return q
def raw(n):return path(n).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def load(n):return json.loads(raw(n))
def check(n,h):require(sha(raw(n))==h,'hash mismatch '+n)
def inventory():
 out=[REPORT]
 for d in (S,E):
  for p in path(d).rglob('*'):
   n=p.relative_to(R).as_posix();path(n)
   if p.is_file():out.append(n)
   else:require(p.is_dir(),'nonregular '+n)
 return sorted(out)
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--preseal',action='store_true');a=ap.parse_args()
 inv=inventory();before={n:sha(raw(n)) for n in inv}
 if a.preseal:require(not any(path(p).exists() for p in EX),'already sealed')
 else:
  seal=load(EX[0]);require(raw(EX[1]).decode()==sha(raw(EX[0]))+'  seal-v1.json\n','anchor')
  require(seal['pin']==PIN and seal['owned_report']==REPORT and seal['owned_directories']==[S,E],'seal identity')
  require(seal['exclusions']==EX and seal['mutable_ledgers']==MUTABLE,'seal exceptions')
  require(inv==sorted([d['path'] for d in seal['files']]+EX),'exact owned domain')
  require([d['path'] for d in seal['files']]==sorted({d['path'] for d in seal['files']}),'canonical manifest')
  for d in seal['files']:check(d['path'],d['sha256']);require(len(raw(d['path']))==d['bytes'],'owned size')
 require(load('sources/upstream.json')['commit']==PIN,'pin')
 inputs=load(S+'/inputs.json');require(sorted(d['path'] for d in inputs)==sorted(MUTABLE+['AGENTS.md']),'input scope')
 drift=[]
 for d in inputs:
  require(d['mutable']==(d['path'] in MUTABLE),'mutable scope');check(d['snapshot'],d['sha256'])
  if sha(raw(d['path']))!=d['sha256']:require(d['mutable'],'immutable input drift');drift.append(d['path'])
 refs=load(S+'/immutable-references.json')
 require([d['path'] for d in refs]==sorted({d['path'] for d in refs}),'canonical refs')
 for d in refs:
  require(not re.search(r'/i9[45][-_]',d['path']),'concurrent output reference')
  check(d['path'],d['sha256']);require(len(raw(d['path']))==d['bytes'],'reference size')
 for lane,h in [('i89_geometric_group_discovery','4d9c2b12ad1bc77dd8c313164e62cc9c9ed80aab1bce82f8cd60de33225a0583'),('i91_finite_cat0_obstruction','ba5e4a80bae104f88eede8df76e0f0f75b05e84bbe185de108347bbc6caa82e8')]:check('frontier/sources/'+lane+'/seal-v1.json',h)
 env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
 p=subprocess.run([sys.executable,'-B','frontier/experiments/i91_finite_cat0_obstruction/verify.py'],cwd=R,env=env,capture_output=True)
 require(p.returncode==0,'original I91 replay '+p.stdout.decode()+p.stderr.decode())
 prior=json.loads(p.stdout);require(prior['status']=='PASS_EVIDENCE_ONLY' and prior['original_blobs_verified']==10373,'historical evidence status')
 require(prior['Q91']=='AUTHOR_PROOF_REQUIRES_INDEPENDENT_REVIEW','historical Q91 verdict changed')
 D=load('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')
 require(len(D)==10373 and len({d['path'] for d in D})==10373,'domain')
 require(len({d['path'].split('/')[1] for d in D})==749,'manuscripts')
 corpus=sorted(d['local'] for d in D if d['kind']=='corpus')
 require(len(corpus)==9340 and sum(d['kind']=='outside_pdf' for d in D)==776,'domain partitions')
 rg=subprocess.check_output(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=R).decode().splitlines()
 require(sorted(rg)==corpus==raw(S+'/corpus-rg-files.txt').decode().splitlines(),'rg corpus inventory')
 qs=load(S+'/searches.json');ps=[re.compile(q['pattern'],re.I) for q in qs];hits=[[] for q in qs]
 for d in sorted(D,key=lambda x:x['path']):
  b=raw(d['local']);require(sha(b)==d['sha256'],'representative '+d['path'])
  for no,line in enumerate(b.decode(errors='replace').splitlines(),1):
   for i,patt in enumerate(ps):
    if patt.search(line):hits[i].append({'path':d['path'],'local':d['local'],'line':no,'text':line})
 for q,h in zip(qs,hits):require(q['count']==len(h) and h==load(q['output']),'search '+q['name'])
 fam={q['name']:sorted({x['path'].split('/')[1] for x in h}) for q,h in zip(qs,hits)}
 require(fam==load(S+'/search-family-index.json'),'search families')
 passages=load(S+'/passages.json')
 for d in passages:
  b=raw(d['path']);require(sha(b)==d['source_sha256'],'passage source');ls=b.decode().splitlines(keepends=True)
  require(1<=d['start']<=d['end']<=len(ls),'range');text=''.join(ls[d['start']-1:d['end']])
  require(sha(text.encode())==d['passage_sha256'],'passage hash')
  require(re.findall(r'\\label\{([^}]+)\}',text)==d['labels'],'labels')
 selected=load(S+'/selected-representatives.json');domain={d['path']:d for d in D}
 require([d['path'] for d in selected]==sorted({d['path'] for d in selected}),'selected canonical')
 for d in selected:require(domain[d['path']]==d,'selected identity')
 def pdf(pdf,txt):
  r=subprocess.run(['pdftotext','-layout',str(path(pdf)),'-'],cwd=R,capture_output=True)
  require(r.returncode==0 and r.stdout==raw(txt),'PDF re-extraction '+pdf)
 selectedpdf=load(S+'/selected-pdf-replays.json')
 for d in selectedpdf:pdf(d['pdf'],d['text'])
 responses=load(S+'/primary/responses.json');npdf=0
 require(len(responses)==14,'response scope')
 for d in responses:
  require(d['status']==200 and d['headers'] and d['captured'] and d['url'] and d['final_url'],'response metadata')
  check(d['local'],d['sha256']);require(len(raw(d['local']))==d['bytes'],'response bytes')
  if 'text' in d:check(d['text'],d['text_sha256']);pdf(d['local'],d['text']);npdf+=1
 for stem,ver in [('toyoda-ann','2404.13871v4'),('toyoda-six','2411.13877v2'),('toyoda-five','1907.09074v3'),('toyoda-fixed','1102.0729v4'),('proximal','1707.09169v1')]:require(ver in raw(S+'/primary/'+stem+'.txt').decode(),'primary PDF version')
 versions=[]
 for f in sorted(path(S+'/primary').glob('*.html')):
  t=f.read_text();versions.append({'path':f.relative_to(R).as_posix(),'submitted_line':re.findall(r'\[Submitted on[^\n]+',t),'history':re.findall(r'.{0,40}\[v\d+\].{0,100}',t)})
 require(versions==load(S+'/primary/versions.json'),'version page replay')
 p=subprocess.run([sys.executable,'-B',str(path(E+'/checks.py'))],cwd=R,env=env,capture_output=True)
 require(p.returncode==0,'independent checks '+p.stderr.decode());result=json.loads(p.stdout)
 require(result==load(E+'/checks-output.json'),'saved independent checks')
 require(inv==inventory() and before=={n:sha(raw(n)) for n in inv},'owned state changed during verification')
 for d in refs:check(d['path'],d['sha256'])
 print(json.dumps({'status':'PASS_PRESEAL_EVIDENCE_ONLY' if a.preseal else 'PASS_EVIDENCE_ONLY','mode':'OFFLINE_READ_ONLY','pin':PIN,'owned_files':len(inv),'immutable_references':len(refs),'passages':len(passages),'original_I91_replay':'PASS_EVIDENCE_ONLY_UNCHANGED_HISTORICAL_VERDICTS','original_blobs_verified':10373,'representative_hashes':len(D),'manuscripts':749,'corpus_originals':9340,'outside_originals':1033,'outside_pdf_hashes':776,'selected_representatives':len(selected),'selected_pdf_reextractions':len(selectedpdf),'new_primary_pdf_reextractions':npdf,'search_hits':{q['name']:len(h) for q,h in zip(qs,hits)},'allowed_live_drift':sorted(drift),'original_proof':'I95_NOT_ASSESSED_OR_BOUND','contribution':'TECHNICAL_CONDITIONAL_ON_I95_ORIGINAL_PROOF_ACCEPTANCE','presentation_output':'NOT_CONSTRUCTED','finding_count_change':0,'symbolic':{k:v for k,v in result['symbolic'].items() if k!='proof'},'trace_slice':{k:v for k,v in result['trace_slice'].items() if k!='update_indices'},'finite_diagnostics':result['finite']},sort_keys=True,indent=2))
if __name__=='__main__':
 try:main()
 except Exception as e:print(json.dumps({'status':'FAIL_EVIDENCE','error':str(e)},sort_keys=True));sys.exit(1)
