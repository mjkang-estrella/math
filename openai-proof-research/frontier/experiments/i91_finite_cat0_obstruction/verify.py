"""Offline READ-ONLY I91 verifier. No fetching, writes, repair, or resealing.

--preseal checks evidence before either seal exists; it never creates a seal.
All ordering uses full POSIX path strings. Python bytecode writes disabled.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i91_finite_cat0_obstruction';E='frontier/experiments/i91_finite_cat0_obstruction'
REPORT='frontier/iterations/i91-finite-cat0-obstruction.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
EX=[S+'/seal-v1.json',S+'/seal-v1.sha256']
MUTABLE=sorted(['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'])
def require(x,s):
 if not x:raise AssertionError(s)
def path(n):
 p=Path(n);require(not p.is_absolute() and '..' not in p.parts,'unsafe path '+n)
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
 inv=inventory()
 if a.preseal:require(not any(path(p).exists() for p in EX),'already sealed')
 else:
  seal=load(EX[0]);require(raw(EX[1]).decode()==sha(raw(EX[0]))+'  seal-v1.json\n','anchor')
  require(seal['pin']==PIN and seal['owned_report']==REPORT and seal['owned_directories']==[S,E],'seal identity')
  require(seal['exclusions']==EX and seal['mutable_ledgers']==MUTABLE,'seal exceptions')
  require(inv==sorted([x['path'] for x in seal['files']]+EX),'exact owned domain')
  require([x['path'] for x in seal['files']]==sorted(x['path'] for x in seal['files']),'canonical order')
  for d in seal['files']:check(d['path'],d['sha256']);require(len(raw(d['path']))==d['bytes'],'owned size')
 inputs=load(S+'/inputs.json');require(sorted(d['path'] for d in inputs)==sorted(MUTABLE+['AGENTS.md']),'input domain')
 drift=[]
 for d in inputs:
  require(d['mutable']==(d['path'] in MUTABLE),'mutable scope');check(d['snapshot'],d['sha256'])
  if sha(raw(d['path']))!=d['sha256']:
   require(d['mutable'],'immutable input drift');drift.append(d['path'])
 refs=load(S+'/immutable-references.json')
 require([d['path'] for d in refs]==sorted({d['path'] for d in refs}),'reference canonical order')
 for d in refs:check(d['path'],d['sha256'])
 require(load('sources/upstream.json')['commit']==PIN,'pin')
 require(sha(raw('frontier/iterations/i89-geometric-group-discovery.md'))=='29adb44728edee78ef949c390de75cb9c486da8860bcf7817898f132bb4f86be','original report')
 require(sha(raw('frontier/sources/i89_geometric_group_discovery/seal-v1.json'))=='4d9c2b12ad1bc77dd8c313164e62cc9c9ed80aab1bce82f8cd60de33225a0583','original seal')
 env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
 # Unmodified historical verifier checks its exact original domain, all
 # 10373 Git blob identities, representative hashes, and original references.
 parent=subprocess.run([sys.executable,'-B','frontier/experiments/i89_geometric_group_discovery/verify.py'],cwd=R,env=env,capture_output=True)
 require(parent.returncode==0,'I89 replay process failure '+parent.stderr.decode())
 prior=json.loads(parent.stdout);require(prior['status']=='PASS_EVIDENCE_ONLY','I89 evidence failure')
 require(prior['original_blobs_verified']==10373 and prior['manuscripts']==749,'complete originals')
 D=load('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')
 require(len(D)==10373 and len({d['path'] for d in D})==10373,'domain identity')
 corpus=sorted(d['local'] for d in D if d['kind']=='corpus')
 rg=subprocess.check_output(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=R)
 require(sorted(rg.decode().splitlines())==raw(S+'/corpus-rg-files.txt').decode().splitlines()==corpus,'corpus inventory')
 qs=load(S+'/searches.json');patterns=[re.compile(q['pattern'],re.I) for q in qs];hits=[[] for q in qs]
 for d in sorted(D,key=lambda x:x['path']):
  b=raw(d['local']);require(sha(b)==d['sha256'],'representative hash '+d['local'])
  for no,line in enumerate(b.decode(errors='replace').splitlines(),1):
   for i,p in enumerate(patterns):
    if p.search(line):hits[i].append({'path':d['path'],'local':d['local'],'line':no,'text':line})
 for q,result in zip(qs,hits):require(len(result)==q['count'] and result==load(q['output']),'search replay '+q['name'])
 passages=load(S+'/passages.json')
 for d in passages:
  b=raw(d['path']);require(sha(b)==d['source_sha256'],'passage source')
  ls=b.decode().splitlines(keepends=True);require(1<=d['start']<=d['end']<=len(ls),'passage range')
  s=''.join(ls[d['start']-1:d['end']]);require(s==d['text'] and sha(s.encode())==d['passage_sha256'],'passage body')
 responses=load(S+'/primary/responses.json');require(len(responses)==2,'new primary scope')
 for d in responses:
  require(d['status']==200 and d['headers'] and d['captured'],'primary response');check(d['local'],d['sha256'])
  require(len(raw(d['local']))==d['bytes'],'primary size')
  if 'text' in d:
   check(d['text'],d['text_sha256'])
   p=subprocess.run(['pdftotext','-layout',str(path(d['local'])),'-'],cwd=R,capture_output=True)
   require(p.returncode==0 and p.stdout==raw(d['text']),'primary PDF replay')
 require('1512.01736v1' in raw(S+'/primary/berg-nikolaev.txt').decode(),'primary version')
 p=subprocess.run([sys.executable,'-B',str(path(E+'/checks.py'))],cwd=R,env=env,capture_output=True)
 require(p.returncode==0,'certificate/diagnostics failure '+p.stderr.decode())
 result=json.loads(p.stdout);require(result==load(E+'/checks-output.json'),'saved checks replay')
 require(inv==inventory(),'verifier changed owned domain')
 if not a.preseal:
  for d in seal['files']:check(d['path'],d['sha256'])
 for d in refs:check(d['path'],d['sha256'])
 print(json.dumps({'status':'PASS_PRESEAL_EVIDENCE_ONLY' if a.preseal else 'PASS_EVIDENCE_ONLY','mode':'OFFLINE_READ_ONLY','pin':PIN,'owned_files':len(inv),'immutable_references':len(refs),'passages':len(passages),'manuscripts':749,'original_blobs_verified':10373,'representative_hashes':len(D),'outside_pdf_hashes':776,'new_primary_pdf_replays':1,'original_I89_replay':'PASS_EVIDENCE_ONLY','search_hits':{q['name']:len(h) for q,h in zip(qs,hits)},'allowed_live_drift':sorted(drift),'original_prerequisites':'ANALYTIC_ORIGINAL_PASS_WITHOUT_REPAIRS_IN_REPORT','Q91':'AUTHOR_PROOF_REQUIRES_INDEPENDENT_REVIEW','contribution':'NOT_CLEARED_NO_SUBSTANTIAL_NOMINATION','presentation_output':'NOT_CONSTRUCTED','finding_count_change':0,**result},sort_keys=True,indent=2))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(json.dumps({'status':'FAIL_EVIDENCE','error':str(e)},sort_keys=True));sys.exit(1)
