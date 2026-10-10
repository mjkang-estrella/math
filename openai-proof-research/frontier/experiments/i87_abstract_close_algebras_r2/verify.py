#!/usr/bin/env python3
"""Offline READ-ONLY I87 verifier: no fetch, writes, repairs or resealing.
Evidence verification is not computation of a mathematical proof verdict.
"""
from pathlib import Path
import hashlib,json,sys,subprocess,os,collections,importlib.util
from concurrent.futures import ThreadPoolExecutor
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i87_abstract_close_algebras_r2'
E='frontier/experiments/i87_abstract_close_algebras_r2'
REPORT='frontier/reviews/i87-abstract-close-algebras-r2.md'
OLD84='frontier/sources/i84_abstract_close_algebras'
EXPECTED84='e493cdc1b840e01e5223b8a3e45cf96cf480313e5c7adc57e0fda0ebb16ed338'
MUTABLE=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
SEAL=S+'/seal-v1.json';ANCHOR=S+'/seal-v1.sha256'
def read(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def js(p):return json.loads(read(p))
def check(ok,msg):
 if not ok:raise AssertionError(msg)
def owned():
 out={REPORT}
 for base in [S,E]:
  check(not (ROOT/base).is_symlink(),'owned root symlink')
  for p in (ROOT/base).rglob('*'):
   check(not p.is_symlink(),'owned symlink '+str(p))
   if p.is_file():out.add(p.relative_to(ROOT).as_posix())
 return out
stats={};drift=[]
try:
 preseal=sys.argv[1:]==['--preseal'];check(not sys.argv[1:] or preseal,'unsupported arguments')
 if preseal:
  check(not (ROOT/SEAL).exists() and not (ROOT/ANCHOR).exists(),'preseal prohibited after sealing')
  stats['unsealed_files']=len(owned())
 else:
  check(sha(read(SEAL))==read(ANCHOR).decode().strip(),'seal anchor')
  seal=js(SEAL);check(seal['owned_report']==REPORT and seal['owned_directories']==[S,E],'ownership declaration')
  check(seal['exclusions']==[SEAL,ANCHOR],'only self-reference exclusions')
  check(owned()==set(seal['files'])|{SEAL,ANCHOR},'exact owned domain')
  for p,h in seal['files'].items():check(sha(read(p))==h,'sealed '+p)
  stats['sealed_files']=len(seal['files'])
 check(sha(read(OLD84+'/seal-v1.json'))==EXPECTED84,'fixed original I84 seal')
 inputs=js(S+'/inputs.json')
 for x in inputs:
  check(sha(read(x['snapshot']))==x['sha256'],'snapshot '+x['path'])
  if sha(read(x['path']))!=x['sha256']:
   check(x['mutable'] and x['path'] in MUTABLE,'immutable input '+x['path']);drift.append(x['path'])
 refs=js(S+'/immutable-references.json')
 check(len({x['path'] for x in refs})==len(refs),'duplicate immutable reference')
 for x in refs:check(sha(read(x['path']))==x['sha256'],'immutable reference '+x['path'])
 stats['immutable_references']=len(refs)
 # Scripts have been inspected for read-only behavior and checked against fixed hashes above.
 # They validate all 10373 Git blobs, 776 extraction identities, original exact owned
 # domains, original content-search multisets, PDF stdout replays and render stdout replays.
 def old_replay(tag,d):
  proc=subprocess.run([sys.executable,'-B',str(ROOT/'frontier/experiments'/d/'verify.py')],cwd=ROOT,capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),timeout=180)
  check(proc.returncode==0,tag+' replay: '+proc.stdout.decode()+proc.stderr.decode())
  check(not proc.stderr,tag+' unexpected stderr')
  result=json.loads(proc.stdout);check(result['evidence']=='PASS' and result['network'] is False and result['read_only'] is True,tag+' evidence flags')
  baseline=js(S+'/'+tag.lower()+'-offline-replay.json');check(baseline['exit_code']==0 and not baseline['stderr'],tag+' retained replay')
  old=json.loads(baseline['stdout'])
  check({k:v for k,v in result.items() if k!='mutable_ledger_drift'}=={k:v for k,v in old.items() if k!='mutable_ledger_drift'},tag+' stable replay result')
  check(set(result['mutable_ledger_drift'])<=set(MUTABLE),tag+' allowed drift only')
  return tag,dict(evidence=result['evidence'],stats=result['stats'],mutable_ledger_drift=result['mutable_ledger_drift'])
 with ThreadPoolExecutor(max_workers=2) as pool:
  futures=[pool.submit(old_replay,*args) for args in [('I84','i84_abstract_close_algebras'),('I82','i82_measured_group_operator_discovery')]]
  stats['inherited_replays']=dict(f.result() for f in futures)
 for p in ['frontier/experiments/i84-parent-verification.json','frontier/experiments/i82-parent-verification.json']:
  x=js(p);check(x['exit_code']==0 and x['result']['evidence']=='PASS','finalized parent wrapper '+p)
 passages=js(S+'/passages.json')
 for x in passages:
  b=read(x['local']);check(sha(b)==x['source_sha256'],'passage source '+x['label'])
  lines=b.decode().splitlines(keepends=True);check(1<=x['start']<=x['end']<=len(lines),'passage range '+x['label'])
  text=''.join(lines[x['start']-1:x['end']]);check(text==x['text'] and sha(text.encode())==x['sha256'],'passage '+x['label'])
 stats['bound_passages']=len(passages)
 actual=next(x for x in passages if x['label']=='CSSWW Theorem 5.4 actual statement and proof')
 check(actual['text'].startswith('Theorem 5.4.') and '10−11' in actual['text'],'corrected CSSWW evidence locator')
 original=next(x for x in passages if x['label']=='Theorem 5.4')
 check(not original['text'].startswith('Theorem 5.4.'),'retain original mislabelled passage')
 spec=importlib.util.spec_from_file_location('i87_search_readonly',ROOT/E/'search.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 config=js(S+'/searches.json');check(config['domain']==mod.DOMAIN and sha(read(mod.DOMAIN))==config['domain_sha256'],'search domain pin')
 domain=js(mod.DOMAIN);check(len(domain)==config['domain_positions']==10373,'domain positions')
 check(sum(x['kind']=='outside_pdf' for x in domain)==config['pdf_representatives']==776,'PDF representative count')
 check({x['name']:x['pattern'] for x in config['searches']}==mod.PATTERNS,'exact search definitions')
 hits=mod.collect();key=lambda x:json.dumps(x,sort_keys=True,ensure_ascii=False)
 for x in config['searches']:
  check(x['flags']=='IGNORECASE','regex flags')
  check(len(hits[x['name']])==x['lines'],'search count '+x['name'])
  check(collections.Counter(map(key,hits[x['name']]))==collections.Counter(map(key,js(x['output']))),'search multiset '+x['name'])
  check(sha(read(x['output']))==x['sha256'],'search body '+x['name'])
 stats['independent_search_lines']={x['name']:x['lines'] for x in config['searches']}
 for x in js(S+'/visual-readings.json'):check(sha(read(x['local']))==x['sha256'],'visually read render binding')
 requests=[json.loads(l) for l in read(OLD84+'/primary-requests.jsonl').decode().splitlines()]
 choi=next(x for x in requests if 'choi-page' in x.get('local',''));check(choi['status']==403,'retained 403')
 powers=next(x for x in requests if 'powers-original-response' in x.get('local',''));b=read(powers['local'])
 check(powers['status']==200 and not b.startswith(b'%PDF') and b'html' in b.lower(),'retained HTML masquerading as PDF')
 scan=read(OLD84+'/primary/haagerup.pdf.txt');check(scan==b'\f'*13,'retained scanned-PDF extraction failure')
 stats['retained_primary_failures']=['HTTP 403 Choi-Christensen','HTTP 200 HTML instead of Powers PDF','Haagerup extraction: 13 form feeds; rendered pages read']
 proc=subprocess.run([sys.executable,'-B',str(ROOT/E/'diagnostics.py')],cwd=ROOT,capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),timeout=60)
 check(proc.returncode==0 and not proc.stderr,'independent diagnostics')
 check(proc.stdout==read(E+'/diagnostics-run-2.stdout'),'exact independent diagnostic replay')
 check(read(E+'/diagnostics-run-2.stderr')==b'','successful diagnostic stderr')
 check(b'AssertionError' in read(E+'/diagnostics-run-1.stderr'),'preserved failed diagnostic')
 stats['independent_diagnostics']=json.loads(proc.stdout)
 print(json.dumps(dict(evidence='PRESEAL PASS' if preseal else 'PASS',review_verdicts_recorded_not_computed=dict(A84='ORIGINAL PASS WITHOUT REPAIRS for every 0<t<1',amplification='ORIGINAL PASS WITHOUT REPAIRS at full stated scope',intrinsic_trace_ideal_invariant='ORIGINAL PASS WITHOUT REPAIRS at stated scope',I82_Proposition_S='ORIGINAL PASS WITHOUT REPAIRS; Q82 not audited'),contribution='TECHNICAL confirmed; not formal substantial clearance; count 8/10 unchanged',stats=stats,mutable_ledger_drift=drift,network=False,read_only=True),indent=2,sort_keys=True))
except Exception as ex:
 print(json.dumps(dict(evidence='FAIL',error=repr(ex),stats=stats,mutable_ledger_drift=drift,network=False,read_only=True),indent=2,sort_keys=True));sys.exit(1)
