"""Offline read-only I131 verifier. Immutable checks precede every finite diagnostic.
One inherited corpus replay, diagnostic callbacks deferred/deduplicated; no repair/reseal.
--preseal validates the unsealed development package and never creates a seal.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json,hashlib,re,runpy,difflib
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i131_soft_summary_stability';E='frontier/experiments/i131_soft_summary_stability'
REPORT='frontier/iterations/i131-soft-summary-stability.md';SEAL=S+'/seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
OLD='frontier/sources/i128_statistical_learning_discovery'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
NAMES=['i113_online_optimization_discovery','i116_robust_prophet_continuation','i119_one_loss_online_selection','i122_variational_free_boundary_discovery','i125_dini_singular_packing','i128_statistical_learning_discovery']
def require(c,m):
 if not c:raise ValueError(m)
def read(p):
 q=Path(p);require(not q.is_absolute() and '..' not in q.parts,'unsafe path '+p)
 q=ROOT/q;require(q.is_file() and not q.is_symlink(),'missing/nonregular '+p);return q.read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def obj(p):return json.loads(read(p))
def check(d):
 b=read(d['path']);require(sha(b)==d['sha256'],'hash '+d['path'])
 if 'bytes' in d:require(len(b)==d['bytes'],'size '+d['path'])
 return b
def owned():
 paths={REPORT}
 for base in [S,E]:
  for p in (ROOT/base).rglob('*'):
   require(not p.is_symlink(),'symlink '+str(p))
   if p.is_file():paths.add(str(p.relative_to(ROOT)))
 return paths
def canonical(rows,actual):
 ps=[d['path'] for d in rows]
 require(ps==sorted(set(ps)),'global canonical inventory')
 require(SEAL not in ps,'seal self-hash forbidden')
 require(set(ps)==actual,'exact owned membership')
 for d in rows:check(d)
def readonly(event,args):
 if event=='open':
  mode,flags=args[1:3]
  require(not(isinstance(mode,str) and any(c in mode for c in 'wax+')),'write forbidden')
  require(not(isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),'write flags forbidden')
 if event.startswith(('socket.','subprocess.')) or event in {'os.system','os.mkdir','os.remove','os.rmdir','os.rename','os.link','os.symlink','os.chmod','os.chown','os.utime','os.truncate','os.exec','os.posix_spawn'}:raise RuntimeError('offline/read-only forbidden: '+event)
def main(preseal=False):
 sys.addaudithook(readonly)
 actual=owned()
 if preseal:
  require(SEAL not in actual,'preseal forbidden after seal')
  inv=[dict(path=p,bytes=len(read(p)),sha256=sha(read(p))) for p in sorted(actual)]
  canonical(inv,actual)
 else:
  seal=obj(SEAL);require(seal['schema']=='i131-exact-owned-v1' and seal['pin']==PIN,'seal metadata')
  require(seal['roots']==[REPORT,S+'/',E+'/'],'seal roots')
  inv=seal['files'];canonical(inv,actual-{SEAL})
  require(seal['validated_inventory_sha256']==sha(json.dumps(inv,sort_keys=True,separators=(',',':')).encode()),'preseal inventory binding')
 require(obj('sources/upstream.json')['commit']==PIN,'upstream identity')
 drift=[];snapshots=obj(S+'/snapshots.json')
 require({d['live'] for d in snapshots if d['drift']}==DRIFT,'only four live ledgers drift')
 for d in snapshots:
  check(dict(path=d['snapshot'],bytes=d['bytes'],sha256=d['sha256']))
  if d['drift']:
   if sha(read(d['live']))!=d['sha256']:drift.append(d['live'])
  else:check(dict(path=d['live'],bytes=d['bytes'],sha256=d['sha256']))
 raw=read('frontier/iterations/iteration128-statistical-learning-discovery-task.json')
 require(sha(raw)=='4479f8966dc9dc118321ca049286ef681a80e44a8c4d70f83c0b333568cb636b','original complete task')
 decoded='\n'.join('FIELD '+k+'\n'+(v if isinstance(v,str) else json.dumps(v,ensure_ascii=False,indent=2)) for k,v in json.loads(raw).items())
 require(decoded==read(S+'/decoded-iteration128-task.txt').decode(),'all decoded task fields')
 refs=obj(S+'/inherited-references.json')
 require([d['path'] for d in refs]==sorted({d['path'] for d in refs}),'flat references canonicality')
 for d in refs:check(d)
 expected={d['path'] for d in obj(OLD+'/inherited-references.json')}
 expected|={d['path'] for d in obj(OLD+'/seal.json')['files']}|{OLD+'/seal.json','frontier/experiments/i128-parent-verification.json'}
 require(expected=={d['path'] for d in refs},'complete flat inherited memberships')
 require(not any(re.search(r'/(?:i|iteration)(?:129|130)(?:[-_/]|\.)',p) for p in expected),'active output dependency')
 verdict=obj(S+'/original-audit-verdicts.json')
 require(verdict['original_report_sha256']==sha(read('frontier/iterations/i128-statistical-learning-discovery.md')),'original audit report')
 require(verdict['inherited']['I125_original_verifier']=='FAIL: ValueError: canonical inventory','retain original failure')
 require(verdict['inherited']['I122_general_Lambda_illustrative_equality'].startswith('FAIL'),'retain I122 failure')
 for d in obj(S+'/reading-references.json'):check(d)
 mapped={d['local']:d for d in obj('frontier/sources/i113_online_optimization_discovery/search-domain.json')}
 selected=obj(S+'/selected-inventory.json')
 require(len(selected)==len({d['local'] for d in selected}),'selection duplicates')
 for d in selected:require(mapped[d['local']]==d,'exact inherited source mapping')
 contracts=[];passages=obj(S+'/read-manifest.json')['passages']
 for d in passages:
  text=check(d).decode('utf8',errors='replace');conv=d['line_convention'];require(conv in ['LF','splitlines'],'line convention')
  ls=text.split('\n') if conv=='LF' else text.splitlines()
  require(len(ls)==d['total_lines'] and 1<=d['start']<=d['end']<=len(ls),'reading bounds')
  require(sha('\n'.join(ls[d['start']-1:d['end']]).encode())==d['passage_sha256'],'passage identity')
  if 'source_path' in d:
   require(mapped[d['path']]['path']==d['source_path'] and mapped[d['path']]['sha256']==d['sha256'],'source contract binding')
   require(d['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['source_path'],'pinned source URL')
   for i in range(d['start'],d['end']+1):
    for m in re.finditer(r'\\label\{[^}]+\}',ls[i-1]):contracts.append(dict(path=d['path'],line=i,needle=m.group(),text=ls[i-1]))
 require(contracts==obj(S+'/source-contracts.json'),'exact labels and multiplicities')
 for name in ['focused-lexical.json','ledger-overlap.json']:
  lex=obj(S+'/'+name);hits=[]
  for p in lex['paths']:
   for i,line in enumerate(read(p).decode().splitlines(),1):
    ms=list(re.finditer(lex['expression'],line,re.I))
    if ms:hits.append(dict(path=p,line=i,text=line,occurrences=[dict(start=m.start(),end=m.end(),text=m.group()) for m in ms]))
  require(hits==lex['hits'],'exact lexical expression/positions/multiplicity '+name)
 extraction=runpy.run_path(str(ROOT/E/'extract_html.py'),run_name='i131_checked_representation')['extract']
 ext=obj(S+'/external-manifest.json')
 for d in ext:
  require(d['status']==200,'successful external retrieval identity');b=check(d)
  if 'versions' in d:require(re.findall(r'\[v[0-9]+\]',b.decode())==d['versions'],'current version list')
  if 'text' in d:require(extraction(b.decode()).encode()==check(d['text']),'HTML representation identity')
 require(next(d['versions'] for d in ext if d['url']=='https://arxiv.org/abs/2609.24931')==['[v1]','[v2]'],'actual Chen v2 version')
 require(next(d['versions'] for d in ext if d['url']=='https://arxiv.org/abs/2609.31797')==['[v1]'],'actual current Ky version')
 cb=obj(S+'/comparison-bindings.json')
 old=extraction(check(cb['old']).decode());new=extraction(check(cb['new']).decode());check(cb['extractor'])
 delta='\n'.join(difflib.unified_diff(old.splitlines(),new.splitlines(),fromfile=cb['old']['path'],tofile='Chen-v2'))
 if cb['diff_final_newline']:delta+='\n'
 require(delta.encode()==check(cb['diff']),'complete current-version diff')
 # I128 performs the single corpus chain. Its final diagnostic callbacks are
 # intercepted here; its own internal deferral continues to run unchanged.
 real=runpy.run_path;pending=[]
 allowed={f'frontier/experiments/{name}/diagnostics.py' for name in NAMES}
 def deferred(path,*args,**kwargs):
  p=str(Path(path).resolve().relative_to(ROOT))
  if p.endswith('/diagnostics.py'):
   require(p in allowed and p not in pending,'unexpected/duplicate finite callback '+p);pending.append(p)
   return {'run':lambda:obj(p[:-3]+'.json')}
  return real(path,*args,**kwargs)
 runpy.run_path=deferred
 try:
  inherited=real(str(ROOT/'frontier/experiments/i128_statistical_learning_discovery/verify.py'),run_name='i131_bound_i128')['main']()
 finally:runpy.run_path=real
 require(set(pending)==allowed,'all six inherited suites deferred')
 require(inherited['corpus_replays']==1,'one corpus replay')
 require(inherited['original_i125_verifier']=='FAIL: ValueError: canonical inventory','original FAIL distinct')
 require(inherited['parent_ordering_only_replay'].startswith('PASS, distinct'),'ordering-only PASS distinct')
 # ALL immutable checks, including the full inherited corpus, have finished.
 results={}
 for p in pending+[E+'/diagnostics.py']:
  result=real(str(ROOT/p),run_name='i131_validated_diagnostic')['run']()
  require(result==obj(p[:-3]+'.json'),'finite identity suite '+p);results[p]=result
 return dict(status='PRESEAL PASS' if preseal else 'PASS',validated_inventory_sha256=sha(json.dumps(inv,sort_keys=True,separators=(',',':')).encode()),offline=True,read_only=True,all_immutable_checks_before_diagnostics=True,corpus_replays=1,corpus=inherited['corpus'],owned_files_excluding_seal=len(inv),inherited_flat_references=len(refs),passages=len(passages),source_contract_occurrences=len(contracts),live_ledger_drift=sorted(drift),original_i125_verifier=inherited['original_i125_verifier'],parent_ordering_only_replay=inherited['parent_ordering_only_replay'],original_i122_general_Lambda='FAIL preserved',current_comparisons=dict(Chen='actual v2; historical v1 retained separately',Ky_Tran='current v1'),finite_diagnostics_once=results,global_S128='unproved/unrefuted; PARK',accepted_count=8,certifies='immutable artifact identities, exact memberships/representations and finite identities only; no universal-proof, novelty or external formal-certification claim')
if __name__=='__main__':
 try:
  require(sys.argv[1:] in [[],['--preseal']],'unknown arguments')
  print(json.dumps(main(bool(sys.argv[1:])),indent=2,sort_keys=True))
 except Exception as ex:
  print(json.dumps(dict(status='FAIL',error=type(ex).__name__+': '+str(ex)),sort_keys=True));sys.exit(1)
