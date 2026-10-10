"""Offline, read-only evidence replay. No network, writes, or seal refresh."""
import pathlib,json,hashlib,subprocess,sys,re,importlib.util
sys.dont_write_bytecode=True
R=pathlib.Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i75_polynomial_twist_selmer';E=R/'frontier/experiments/i75_polynomial_twist_selmer'
REPORT=R/'frontier/iterations/i75-polynomial-twist-selmer.md'
LEDGERS={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def readj(p):return json.loads(p.read_text())
def run(cmd):
 z=subprocess.run(cmd,cwd=R,capture_output=True)
 assert z.returncode==0,(cmd,z.returncode,z.stderr.decode(errors='replace'))
 return z

def verify(preflight=False):
 out={'status':'PASS_PROVENANCE_AND_EXACT_FINITE_INTERFACES','mathematics':'C73-D and C73-M remain unproved and unrefuted; no substantial nomination; conditional inequalities are not verified theorems.'}
 actual={str(p.relative_to(R)) for base in [S,E] for p in base.rglob('*') if p.is_file() and p!=S/'seal-v1.json'}|{str(REPORT.relative_to(R))}
 if not preflight:
  seal=readj(S/'seal-v1.json');assert seal['version']==1
  assert set(seal['files'])==actual,{'missing':sorted(set(seal['files'])-actual),'extra':sorted(actual-set(seal['files']))}
  for name,digest in seal['files'].items():assert sha((R/name).read_bytes())==digest,name
  out['sealed_files']=len(actual)
 refs=readj(S/'prior-references.json')
 for r in refs:
  assert r['path'] not in LEDGERS
  assert sha((R/r['path']).read_bytes())==r['sha256'],r['path']
 out['immutable_prior_references']=len(refs)
 ledgers=readj(S/'ledgers.json');assert {r['path'] for r in ledgers}==LEDGERS
 drift=[]
 for r in ledgers:
  assert sha((S/'ledgers'/r['path']).read_bytes())==r['sha256']
  if sha((R/r['path']).read_bytes())!=r['sha256']:drift.append(r['path'])
 out['informational_mutable_ledger_drift']=sorted(drift)
 task=readj(R/'frontier/iterations/iteration75-polynomial-twist-selmer-task.json')
 assert (S/'brief.txt').read_text()==task['brief']
 assert (S/'complete-message.txt').read_text()==('Act as the research sub-agent for this task.\n\n'+task['brief']).removesuffix('\n')
 out['complete_brief']='exact parent brief plus recovered role sentence, original message has no trailing LF'
 passages=readj(S/'passages.json')
 for p in passages:
  lines=(R/p['path']).read_bytes().splitlines(keepends=True);lo,hi=p['lines'];assert 1<=lo<=hi<=len(lines)
  assert sha(b''.join(lines[lo-1:hi]))==p['sha256'],p
 out['passages']=len(passages)
 requests=readj(S/'requests.json')+readj(S/'requests-extra.json')+[readj(S/'request-pin.json')]
 pdf_replays=0
 for q in requests:
  assert q.get('status')==200 and 'error' not in q,q
  p=R/q['path'];b=p.read_bytes();assert len(b)==q['bytes'] and sha(b)==q['sha256'],q['path']
  if p.suffix=='.pdf':
   z=run(['pdftotext','-layout',str(p),'-']);assert z.stdout==p.with_suffix('.txt').read_bytes(),p
   assert z.stderr.decode()==q['extraction_stderr'];pdf_replays+=1
  if 'pin_path' in q:
   assert b==(R/q['pin_path']).read_bytes()
   assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==q['git_blob']
 versions=readj(S/'versions.json')
 for name,v in versions.items():
  nums=re.findall(r'\[v(\d+)\]',(S/'primary'/(name+'.html')).read_text())
  assert nums==v['versions'] and max(map(int,nums))==v['latest']
 out.update(successful_retained_requests=len(requests),new_pdf_text_replays=pdf_replays,capture_time_versions={k:v['latest'] for k,v in versions.items()},fresh_raw_pin_comparisons=1)
 renders=readj(S/'render-bindings.json')
 for r in renders:
  b=run(['pdftoppm','-f',str(r['page']),'-l',str(r['page']),'-r',str(r['dpi']),'-png','-singlefile',str(R/r['pdf'])]).stdout
  assert b==(R/r['path']).read_bytes() and sha(b)==r['sha256'],r['path']
 out['scanned_primary_page_replays']=len(renders)
 spec=importlib.util.spec_from_file_location('i75_diag',E/'diagnostics.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 result=mod.run();assert result==readj(E/'diagnostics.json')
 out['finite_diagnostics']=result['status'];out['actual_curve_checks']={'d65537':{'pure_2_dimension':2,'a_T':32,'analytic_rank_from_Tunnell':0},'d262145':{'pure_2_dimension':4,'a_T':0,'non_torsion_point':[-1024,-8388576],'analytic_rank_lower_bound':2}}
 old=run([sys.executable,'-B','frontier/experiments/i73_arithmetic_geometry_discovery/verify.py']);old_result=json.loads(old.stdout)
 assert old_result['status']=='PASS_PROVENANCE_AND_FINITE_INTERFACES'
 assert old_result['corpus_files']==9340 and old_result['other_tree_blobs']==1033
 assert old_result['pinned_text_files']==237 and old_result['old_new_TeX_pairs']==48
 out['unchanged_i73_replay']=old_result
 if preflight:out['phase']='pre-seal checks; self-seal not checked yet'
 return out
if __name__=='__main__':
 assert set(sys.argv[1:])<= {'--preflight'}
 print(json.dumps(verify('--preflight' in sys.argv),indent=2,sort_keys=True))
