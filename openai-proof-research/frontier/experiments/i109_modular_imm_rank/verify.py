"""Offline READ-ONLY integrity/finite-diagnostic verifier. Run python -B.
No network, process, write, bytecode, extraction, repair or resealing operations.
--preseal checks all dependencies and computations before a separate final seal.
"""
import sys
sys.dont_write_bytecode=True
import pathlib,json,hashlib,re,collections,runpy,os
R=pathlib.Path(__file__).resolve().parents[3]
S=pathlib.Path('frontier/sources/i109_modular_imm_rank')
X=pathlib.Path('frontier/experiments/i109_modular_imm_rank')
REPORT=pathlib.Path('frontier/iterations/i109-modular-imm-rank.md')
OLD=pathlib.Path('frontier/sources/i106_positive_characteristic_imm')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
OLD_SEAL='07ef9184bb8484e4e90677f4bd8781f574c52f538542ee095d8a0dae91129e43'
ALLOW={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def guard(event,args):
 if event=='open':
  mode,flags=args[1],args[2]
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
   raise RuntimeError('Read-only verifier blocked write')
 if event.startswith(('socket.','subprocess.')) or event in {'os.system','os.remove','os.unlink','os.rename','os.rmdir','os.mkdir','os.chmod','os.link','os.symlink','os.truncate','os.utime'}:
  raise RuntimeError('Read-only/offline verifier blocked '+event)
sys.addaudithook(guard)
def raw(p):return (R/p).read_bytes()
def sha(p):return hashlib.sha256(raw(p)).hexdigest()
def data(p):return json.loads(raw(p))
def check(ok,msg):
 if not ok:raise AssertionError(msg)
def inventory():
 out=[str(REPORT)]
 for base in [S,X]:
  for p in (R/base).rglob('*'):
   check(not p.is_symlink(),'owned symlink '+str(p))
   if p.is_file():out.append(str(p.relative_to(R)))
 return sorted(out)
def main():
 check(sys.argv[1:] in [[],['--preseal']],'arguments')
 pre=bool(sys.argv[1:]);sp=str(S/'seal.json');files=inventory()
 if pre:check(not (R/sp).exists(),'seal already exists')
 else:
  seal=data(sp);check(seal['pin']==PIN,'pin');check(set(files)==set(seal['files'])|{sp},'exact owned inventory')
  for p,h in seal['files'].items():check(sha(p)==h,'owned hash '+p)
 refs=data(S/'immutable-references.json');drift=[]
 for d in refs:
  p=d['path'];check('i107_' not in p and 'i108_' not in p and 'i107-' not in p and 'i108-' not in p,'active output bound')
  if 'snapshot' in d:check(sha(d['snapshot'])==d['sha256'],'snapshot '+p)
  if d['drift_allowed']:
   check(p in ALLOW,'extra drift permission')
   if sha(p)!=d['sha256']:drift.append(p)
  else:check(sha(p)==d['sha256'],'immutable reference '+p)
 check(sha(OLD/'seal.json')==sha(S/'original-seal.json')==OLD_SEAL,'frozen I106 seal')
 task=data(S/'snapshots/frontier/iterations/iteration109-modular-imm-rank-task.json')
 check(raw(S/'complete-launch-brief.txt').decode()==task['brief'],'complete brief')
 check(raw(S/'complete-additional-instructions.txt').decode()==task['additional_instructions'],'complete additional directions')
 _,brief=task['brief'].split('--- ORIGINAL I106 BRIEF ---',1)
 ob,rem=brief.split('--- ORIGINAL I106 REPORT ---',1);orr,op=rem.split('--- FINAL PARENT RESPONSE ---',1)
 check(ob==raw(S/'original-brief.txt').decode(),'verbatim original brief section')
 check(orr==raw(S/'original-report.txt').decode(),'verbatim original report section')
 check(op==raw(S/'original-parent.txt').decode(),'verbatim original final parent section')
 check(ob.strip()==data(S/'snapshots/frontier/iterations/iteration106-positive-characteristic-imm-task.json')['brief'].strip(),'original brief identity')
 check(orr.strip()==raw(S/'snapshots/frontier/iterations/i106-positive-characteristic-imm.md').decode().strip(),'original report identity')
 check(json.loads(op)==data(S/'snapshots/frontier/experiments/i106-parent-verification.json'),'original parent identity')
 oldseal=data(OLD/'seal.json')
 for p,h in oldseal['files'].items():check(sha(p)==h,'I106 original inventory hash '+p)
 argv=sys.argv[:]
 try:
  sys.argv=[str(R/'frontier/experiments/i106_positive_characteristic_imm/verify.py')]
  inherited=runpy.run_path(sys.argv[0])['main']()
 finally:sys.argv=argv
 check(inherited['status']=='PASS','I106/I103 inherited replay')
 domain=data(pathlib.Path('frontier/sources/i103_algebraic_complexity_discovery/search-domain.json'))
 queries=data(S/'queries.json');compiled={k:re.compile(v) for k,v in queries.items()};hits=[]
 for d in domain:
  for ln,line in enumerate(raw(d['local']).decode(errors='replace').splitlines(),1):
   for key,expr in compiled.items():
    for m in expr.finditer(line):hits.append({'query':key,'path':d['path'],'line':ln,'start':m.start(),'end':m.end(),'text':line})
 expected=[json.loads(line) for line in raw(S/'lexical-hits.jsonl').decode().splitlines()]
 check(hits==expected,'exact ordered lexical occurrence multiset')
 sm=data(S/'search-summary.json');check(sm['positions']==len(domain)==10373 and sm['manuscripts']==749 and sm['tree_entries']==13223 and sm['occurrences']==len(hits),'search summary')
 check(dict(collections.Counter(h['path'].split('/')[1] for h in hits))==data(S/'lexical-family-summary.json'),'lexical families')
 for d in data(S/'read-manifest.json'):
  check(sha(d['path'])==d['source_sha256'],'reading source hash '+d['path'])
  check(d['line_convention'].startswith('LF;'),'read convention')
  ls=raw(d['path']).decode().split('\n');a,z=d['first'],d['last'];check(1<=a<=z<=len(ls),'read interval')
  check(hashlib.sha256(('\n'.join(ls[a-1:z])+'\n').encode()).hexdigest()==d['passage_sha256'],'passage hash '+d['path'])
  if 'upstream_path' in d:check(d['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['upstream_path'],'source URL')
 for d in data(S/'external-requests.json'):
  if 'sha256' in d:check(sha(S/'external'/d['name'])==d['sha256'],'external bytes')
  if d.get('extraction_exit')==0:check(sha(S/'external'/d['name'].replace('.pdf','.txt'))==d['text_sha256'],'external extract bytes')
 diagnostics=runpy.run_path(str(R/X/'check_math.py'))['run']();check(diagnostics==data(X/'exact-results.json'),'exact diagnostics')
 return {'status':'PRESEAL_PASS' if pre else 'PASS','scope':'Evidence integrity and finite diagnostics only; not universal proof or substantiality certification','owned_files':len(files),'original_i106_seal_sha256':OLD_SEAL,'original_i106_replay':inherited,'new_lexical_occurrences':len(hits),'read_passages':len(data(S/'read-manifest.json')),'exact_diagnostics':diagnostics,'allowed_live_ledger_drift':drift}
if __name__=='__main__':
 try:print(json.dumps(main(),indent=2))
 except Exception as e:
  print(json.dumps({'status':'FAIL','error':type(e).__name__+': '+str(e)}));raise
