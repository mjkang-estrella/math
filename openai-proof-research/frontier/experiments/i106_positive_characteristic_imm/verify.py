"""Offline READ-ONLY integrity and exact finite diagnostics. No proof certification.
Run python -B. --preseal validates before a separate preparation step seals.
"""
import sys
sys.dont_write_bytecode=True
import pathlib,json,hashlib,re,runpy,collections,os
R=pathlib.Path(__file__).resolve().parents[3]
S=pathlib.Path('frontier/sources/i106_positive_characteristic_imm')
X=pathlib.Path('frontier/experiments/i106_positive_characteristic_imm')
REPORT=pathlib.Path('frontier/iterations/i106-positive-characteristic-imm.md')
OLD=pathlib.Path('frontier/sources/i103_algebraic_complexity_discovery')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
ALLOW={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def guard(event,args):
 if event=='open':
  mode=args[1];flags=args[2]
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
   raise RuntimeError('Read-only verifier blocked file write')
 if event.startswith(('socket.','subprocess.')) or event in {'os.system','os.remove','os.unlink','os.rename','os.rmdir','os.mkdir','os.chmod','os.link','os.symlink','os.truncate'}:
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
   check(not p.is_symlink(),'owned symlink')
   if p.is_file():out.append(str(p.relative_to(R)))
 return sorted(out)
def main():
 check(sys.argv[1:] in [[],['--preseal']],'arguments')
 pre=bool(sys.argv[1:]);sealpath=str(S/'seal.json');files=inventory()
 if pre:check(not (R/sealpath).exists(),'seal already exists')
 else:
  seal=data(sealpath);check(seal['pin']==PIN,'pin')
  check(set(files)==set(seal['files'])|{sealpath},'exact owned inventory')
  for p,h in seal['files'].items():check(sha(p)==h,'owned hash '+p)
 refs=data(S/'immutable-references.json');drift=[]
 for item in refs:
  p=item['path'];check('i104_' not in p and 'i105_' not in p,'active output reference')
  if 'snapshot' in item:check(sha(item['snapshot'])==item['sha256'],'snapshot '+p)
  if item['drift_allowed']:
   check(p in ALLOW,'extra drift allowance')
   if sha(p)!=item['sha256']:drift.append(p)
  else:check(sha(p)==item['sha256'],'immutable '+p)
 check(sha(OLD/'seal.json')==sha(S/'original-seal.json')=='b3eaa8ec05a4bb443476b61d2af487ee73fb2393b992fef3ccfb572a8b59949f','original seal')
 check(raw(S/'original-report.txt')==raw(S/'snapshots/frontier/iterations/i103-algebraic-complexity-discovery.md'),'verbatim original report')
 check(raw(S/'original-brief.txt').decode().strip()==data(S/'snapshots/frontier/iterations/iteration103-algebraic-complexity-discovery-task.json')['brief'].strip(),'original brief')
 check(data(S/'original-parent.json')==data(S/'snapshots/frontier/experiments/i103-parent-verification.json'),'parent JSON')
 # Immutable old verifier, itself bound by immutable original seal. It independently
 # checks every original blob, inherited extracts, all old references and diagnostics.
 oldseal=data(OLD/'seal.json')
 for p,h in oldseal['files'].items():check(sha(p)==h,'original owned hash '+p)
 argv=sys.argv[:]
 try:
  sys.argv=[str(R/'frontier/experiments/i103_algebraic_complexity_discovery/verify.py')]
  original=runpy.run_path(sys.argv[0])['main']()
 finally:sys.argv=argv
 check(original['status']=='PASS','original integrity replay')
 domain=data(OLD/'search-domain.json');queries=data(S/'queries.json');compiled={k:re.compile(v) for k,v in queries.items()};hits=[]
 for d in domain:
  for ln,line in enumerate(raw(d['local']).decode(errors='replace').splitlines(),1):
   for key,expr in compiled.items():
    for m in expr.finditer(line):hits.append({'query':key,'path':d['path'],'line':ln,'start':m.start(),'end':m.end(),'text':line})
 expected=[json.loads(x) for x in raw(S/'lexical-hits.jsonl').decode().splitlines()]
 check(hits==expected,'exact ordered lexical occurrence multiset')
 summary=data(S/'search-summary.json');counts=dict(collections.Counter(x['query'] for x in hits))
 check(summary['positions']==10373 and summary['manuscripts']==749 and summary['counts']==counts,'search summary')
 refined=data(S/'refined-screen.json');filtered=[x for x in hits if x['query']=='imm' and re.search(refined['expression'],x['text'])]
 check(filtered==refined['occurrences'],'refined exact multiset')
 check(dict(collections.Counter(x['path'].split('/')[1] for x in filtered))==refined['families'],'refined family counts')
 for rd in data(S/'read-manifest.json'):
  check(sha(rd['path'])==rd['source_sha256'],'read source '+rd['path'])
  ls=raw(rd['path']).decode().split('\n') if rd['line_convention'].startswith('LF;') else raw(rd['path']).decode().splitlines()
  a,z=rd['first'],rd['last'];check(1<=a<=z<=len(ls),'read range')
  check(hashlib.sha256(('\n'.join(ls[a-1:z])+'\n').encode()).hexdigest()==rd['passage_sha256'],'passage hash')
  if 'upstream_path' in rd:check(rd['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+rd['upstream_path'],'pinned URL')
 for rd in data(S/'external-requests.json'):
  if rd.get('extraction_exit')==0:
   check(sha(S/'external'/(rd['name']+'.pdf'))==rd['sha256'],'PDF byte binding')
   check(sha(S/'external'/(rd['name']+'.txt'))==rd['text_sha256'],'extract byte binding')
 math=runpy.run_path(str(R/X/'check_math.py'))['run']()
 check(math==data(X/'exact-results.json'),'exact finite diagnostics')
 return {'status':'PRESEAL_PASS' if pre else 'PASS','scope':'Evidence integrity and finite diagnostics only; no universal mathematical or substantiality certification','owned_files':len(files),'original_seal_sha256':sha(OLD/'seal.json'),'original_replay':original,'lexical_counts':counts,'refined_occurrences':len(filtered),'read_passages':len(data(S/'read-manifest.json')),'exact_diagnostics':math,'allowed_live_ledger_drift':drift}
if __name__=='__main__':
 try:print(json.dumps(main(),indent=2))
 except Exception as e:
  print(json.dumps({'status':'FAIL','error':type(e).__name__+': '+str(e)}));raise
