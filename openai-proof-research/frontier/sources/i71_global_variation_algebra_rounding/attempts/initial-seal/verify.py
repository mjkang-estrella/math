"""Read-only offline I71 evidence verifier. PASS is not analytic acceptance.

No network, writers, prior diagnostic imports, or seal refreshes. The old I69
verifier is run unchanged to replay the hash-referenced tree/corpus interfaces.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,os,re,subprocess,sys
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i71_global_variation_algebra_rounding'
X=R/'frontier/experiments/i71_global_variation_algebra_rounding'
REPORT=R/'frontier/iterations/i71-global-variation-algebra-rounding.md'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def ck(test,message):
 if not test:raise AssertionError(message)
def sha(b):return hashlib.sha256(b).hexdigest()
def js(p):return json.loads(p.read_bytes())
def path(s):
 p=R/s;ck(p.resolve().is_relative_to(R),'outside project');return p
def checked(p,h):
 b=path(p).read_bytes();ck(sha(b)==h,'hash mismatch: '+p);return b
def run(args):
 env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
 return subprocess.run(args,cwd=R,env=env,capture_output=True)
def main():
 seal=js(S/'seal.json');ck(seal['pinned_commit']==PIN,'pin')
 expected={z['path']:z['sha256'] for z in seal['files']}
 exclude={S/'seal.json',S/'verification.json'}
 actual={str(p.relative_to(R)) for base in [S,X] for p in base.rglob('*') if p.is_file() and p not in exclude}
 actual.add(str(REPORT.relative_to(R)))
 ck(actual==set(expected),'sealed file set')
 for p,h in expected.items():checked(p,h)
 refs=js(S/'references.json')+js(S/'additional-references.json')
 ck(len({r['path'] for r in refs})==len(refs),'duplicate references')
 ck({r['path'] for r in refs if r['mutable']}==MUTABLE,'exact four-ledger allowlist')
 drift=[]
 for r in refs:
  if r['mutable']:
   frozen=S/'ledgers'/r['path'];ck(sha(frozen.read_bytes())==r['sha256'],'frozen ledger')
   if sha(path(r['path']).read_bytes())!=r['sha256']:drift.append(r['path'])
  else:checked(r['path'],r['sha256'])
 task=js(R/'frontier/iterations/iteration71-global-variation-algebra-rounding-task.json')
 ck((S/'brief.txt').read_text()==task['brief'],'exact full inherited brief')
 ck(js(R/'sources/upstream.json')['commit']==PIN,'upstream commit')
 # Unchanged prior replay verifies corpus hashes, pins, original failures and
 # exact domains, including the 1033 blobs outside the fixed corpus.
 old=run([sys.executable,'-B','frontier/experiments/i69_global_algebra_rounding_budget/verify.py'])
 ck(old.returncode==0,'unchanged I69 replay failed: '+old.stderr.decode())
 old_result=json.loads(old.stdout)
 saved=js(S/'i69-readonly-replay.json')
 for k,v in {'status':'PASS','sealed_artifacts':78,'corpus_blobs':9340,'tree_blobs':10373,'tree_entries':13223,'manuscripts':749,'tree_blobs_outside_fixed_corpus':1033,'pinned_files':26,'exact_assertions':61237,'floating_records':10}.items():
  ck(old_result[k]==saved[k]==v,'old replay count: '+k)
 cp='frontier/sources/i14_spectral_width_novelty_r3/corpus'
 searches=js(S/'searches.json');counts={}
 for rec in searches:
  p=run(['rg','--no-ignore','-n',rec['pattern'],cp])
  ck(p.returncode==rec['returncode'],'search status')
  ck(p.stderr.decode()==rec['stderr'],'search stderr')
  lines=js(S/(rec['name']+'-search.json'))
  ck(Counter(p.stdout.decode().splitlines())==Counter(lines),'fixed-domain line multiset: '+rec['name'])
  ck(len(lines)==rec['count'],'search count');counts[rec['name']]=len(lines)
 primary=js(S/'primary/manifest.json');pdfs=0;failures=[]
 for rec in primary:
  if 'error' in rec:
   failures.append(rec['error'])
   if 'path' in rec:checked(rec['path'],rec['sha256'])
   continue
  b=checked(rec['path'],rec['sha256']);ck(len(b)==rec['bytes'] and rec['status']==200,'HTTP record')
  if 'text_path' in rec:
   txt=checked(rec['text_path'],rec['text_sha256'])
   p=run(['pdftotext','-layout',rec['path'],'-'])
   ck(p.returncode==rec['extract_status']==0,'PDF status')
   ck(p.stdout==txt,'PDF replay');ck(p.stderr.decode()==rec['extract_stderr'],'PDF stderr')
   pdfs+=1
 for rec in js(S/'versions.json'):
  b=checked(rec['path'],rec['sha256']);txt=b.decode()
  ck(re.findall(r'arXiv:\s*[^\s\[]+',txt[:5000])==rec['served_markers'],'served version marker')
  ck(txt.splitlines()[:25]==rec['first_lines'],'version header')
 passages=js(S/'passages.json')+js(S/'supplementary-passages.json')
 for rec in passages:
  b=checked(rec['path'],rec['file_sha256'])
  piece=b''.join(b.splitlines(keepends=True)[rec['first_line']-1:rec['last_line']])
  ck(sha(piece)==rec['passage_sha256'],'passage binding')
 p=run([sys.executable,'-B',str(X/'diagnostics.py')])
 ck(p.returncode==0 and not p.stderr,'diagnostics failed')
 ck(p.stdout==(S/'diagnostics.json').read_bytes(),'diagnostic byte replay')
 d=json.loads(p.stdout)
 out=dict(status='PASS',scope='Offline evidence and finite diagnostics only; not a universal proof, independent analytic acceptance or novelty certificate.',sealed_artifacts=len(expected),immutable_references=sum(not r['mutable'] for r in refs),mutable_allowlist=sorted(MUTABLE),allowed_live_ledger_drift=sorted(drift),exact_full_brief=True,prior_i69_replay='Unchanged PASS',tree_entries=13223,manuscripts=749,tree_blobs=10373,fixed_corpus_files=9340,outside_corpus_blobs=1033,search_line_multisets=counts,primary_responses=len(primary)-len(failures),primary_failures=failures,pdf_replays=pdfs,passage_bindings=len(passages),exact_assertions=d['exact_assertions'],floating_records=len(d['floating_records']),analytic_disposition='AR_K open; no nomination; technical partials and method obstructions only')
 print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
