"""Offline read-only I151 evidence replay. One flat corpus traversal; no ancestor execution.
Only the new finite diagnostics run, after every immutable byte has been checked.
No repair/reseal interface. --preseal is validation before the single external seal.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json,hashlib,re
from collections import Counter
from fractions import Fraction
from itertools import combinations
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i151_spatial_dynamical_percolation_continuation'
E='frontier/experiments/i151_spatial_dynamical_percolation_continuation'
REPORT='frontier/iterations/i151-spatial-dynamical-percolation-continuation.md'
SEAL=S+'/seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
cache={};identities={};keep=set();phase='immutable'
def require(v,m):
 if not v:raise ValueError(m)
def audit(event,args):
 if event=='open':
  mode,flags=args[1:3]
  require(not(isinstance(mode,str) and any(c in mode for c in 'wax+')),'write denied')
  require(not(isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),'write flags denied')
 require(not event.startswith(('socket.','subprocess.','urllib.','http.client.','ctypes.')),'network/subprocess/native escape denied')
 require(event not in {'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.truncate','os.link','os.symlink','os.utime','os.exec','os.posix_spawn','os.fork','os.putenv'},'mutation/process denied')
sys.addaudithook(audit)
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p,retain=True):
 if p in cache:return cache[p]
 require(phase=='immutable','unloaded bytes after immutable phase: '+p)
 require(p not in identities,'duplicate evicted read: '+p)
 q=Path(p);require(not q.is_absolute() and '..' not in q.parts,'unsafe path')
 q=ROOT/q;require(q.is_file() and not q.is_symlink(),'nonregular: '+p)
 b=q.read_bytes();identities[p]={'bytes':len(b),'sha256':sha(b),'git_sha':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
 if retain or p in keep:cache[p]=b
 return b
def obj(p):return json.loads(read(p))
def check(p,h,size=None,retain=True):
 if p not in identities:read(p,retain)
 r=identities[p];require(r['sha256']==h,'immutable hash: '+p)
 if size is not None:require(r['bytes']==size,'immutable size: '+p)
 return r
def owned():
 ps={REPORT}
 for root in (S,E):
  for p in (ROOT/root).rglob('*'):
   require(not p.is_symlink(),'owned symlink')
   if p.is_file():ps.add(str(p.relative_to(ROOT)))
 return ps
def inventory():return [{'path':p,'sha256':identities[p]['sha256'],'bytes':identities[p]['bytes']} for p in sorted(owned()-{SEAL})]
def invhash(rows):return sha(json.dumps(rows,sort_keys=True,separators=(',',':')).encode())
def decode(d):return '\n'.join('FIELD '+k+'\n'+(v if isinstance(v,str) else json.dumps(v,ensure_ascii=False,indent=2)) for k,v in d.items())
def main(preseal):
 global phase
 if preseal:
  require(not (ROOT/SEAL).exists(),'prevalidation only before one seal')
  for p in sorted(owned()):read(p)
 else:
  se=obj(SEAL);require(se['schema']=='i151-exact-owned-v1' and se['pin']==PIN,'seal schema/pin')
  require(se['roots']==[REPORT,S+'/',E+'/'],'owned roots')
  rows=se['files'];ps=[r['path'] for r in rows]
  require(ps==sorted(set(ps)) and set(ps)|{SEAL}==owned(),'exact canonical inventory')
  for r in rows:check(r['path'],r['sha256'],r['bytes'])
  require(invhash(rows)==se['validated_inventory_sha256'],'prevalidated digest')
 idx=obj(S+'/reading-index.json');ctx=obj(S+'/context-reading-plan.json')
 keep.update(r['path'] for r in idx['passages']);keep.update(r['path'] for r in ctx['files'])
 flat=obj(S+'/immutable-flat.json')['files'];require([r['path'] for r in flat]==sorted({r['path'] for r in flat}),'flat canonical inventory')
 for r in flat:check(r['path'],r['sha256'],r['bytes'])
 domain=obj('frontier/sources/i113_online_optimization_discovery/search-domain.json');tree=obj('sources/preprints-tree.json')
 require(obj('sources/upstream.json')['commit']==PIN,'stipulated pin')
 require(len(tree['tree'])==13223 and not tree.get('truncated'),'full tree')
 require(len({r['path'].split('/')[1] for r in tree['tree']})==749,'manuscript membership')
 blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
 require(len(domain)==len(blobs)==10373 and {r['path'] for r in domain}==set(blobs),'complete original map')
 require(Counter(r['kind'] for r in domain)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'map kinds')
 # The single flat traversal, with duplicate references resolved from identities.
 for r in domain:
  d=check(r['original_local'],r['original_sha256'],retain=False)
  require(d['git_sha']==r['git_sha']==blobs[r['path']],'pinned git blob: '+r['path'])
  check(r['local'],r['sha256'],retain=False)
 actual={str(p.relative_to(ROOT)) for p in (ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus').rglob('*') if p.is_file()}
 require(actual=={r['original_local'] for r in domain if r['kind']=='corpus'},'exact corpus membership')
 require(len({r['original_local'] for r in domain})==10373,'unique originals')
 phase='representations'
 require(domain==obj('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'),'I88 map identity')
 require([{k:r[k] for k in ('path','local','kind','sha256')} for r in domain]==obj('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json'),'I79 map identity')
 req={r['path']:r for r in map(json.loads,read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').splitlines()) if r.get('status')==200}
 for r in domain:
  if r['kind']=='outside_pdf':
   x=req[r['path']];ex=x['extraction']
   require(x['local']==r['original_local'] and x['sha256']==r['original_sha256'] and x['git_match'],'PDF original binding')
   require(ex['code']==0 and ex['path']==r['local'] and ex['sha256']==r['sha256'],'PDF extraction binding')
 # Every declared passage and its real ending; duplicates are not extra coverage.
 scope={};passages=[]
 for plan in idx['plans']:
  for r in obj(plan):passages.append({**r,'plan':plan})
 require(passages==idx['passages'],'exact plan index')
 for r in passages:
  require(r['read'] is True,'unread declared passage')
  check(r['path'],r['sha256']);ls=read(r['path']).decode().splitlines()
  require(1<=r['start']<=r['end']<=len(ls),'range: '+r['path'])
  require(r['ending']==ls[r['end']-1],'actual ending')
  require(sha('\n'.join(ls[r['start']-1:r['end']]).encode())==r['passage_sha256'],'passage hash')
  scope.setdefault(r['path'],set()).update(range(r['start'],r['end']+1))
 for r in obj(S+'/read-manifest.json')['passages']:
  check(r['path'],r['file_sha256']);ls=read(r['path']).decode().splitlines()
  require(r['ending']==ls[r['end']-1] and sha('\n'.join(ls[r['start']-1:r['end']]).encode())==r['passage_sha256'],'initial mandatory passage')
 for name in ('family-operation-reading-plan.json','pressure-companion-reading-plan.json','prior-reading-plan.json','gps-dynamics-reading-plan.json','van-spectral-reading-plan.json','van-quenched-reading-plan.json','van-annealed-reading-plan.json'):
  for p in {r['path'] for r in obj(S+'/'+name)}:
   require(scope[p]==set(range(1,len(read(p).decode().splitlines())+1)),'complete declared operation file: '+p)
 # All decoded fields, including metadata; all original JSON references frozen.
 for r in ctx['files']:
  check(r['path'],r['sha256']);ls=read(r['path']).decode().splitlines()
  require(len(ls)==r['lines'],'context lines')
  scope.setdefault(r['path'],set()).update(range(1,len(ls)+1))
  if r['path'].endswith('.decoded.txt'):
   p=r['path'].replace('.decoded.txt','.json')
   require(read(r['path']).decode()==decode(obj(p)),'all decoded fields: '+p)
   orig='frontier/iterations/'+Path(p).name
   require(read(p)==read(orig),'original record snapshot: '+orig)
 require(identities['frontier/iterations/iteration149-spectral-stochastic-universality-discovery-task.json']['sha256']=='12378ffe25d5d800bc9d343ee5f58953ead19348267d78236f62197a24d2e150','mandatory I149')
 require(identities['frontier/iterations/iteration146-effective-boundary-exclusion-task.json']['sha256']=='19d84d4dc9e9609ce93883a43aae46d44252dc601f020ea360d2daa9db312027','mandatory I146')
 expected={}
 for r in ctx['files']:
  for n,line in enumerate(read(r['path']).decode().splitlines(),1):expected.setdefault(line,[]).append({'path':r['path'],'line':n})
 require(len(expected)==len(ctx['groups'])==3342,'exact context dedup cardinality')
 seen=set()
 for g in ctx['groups']:
  a=g['representative'];line=read(a['path']).decode().splitlines()[a['line']-1]
  require(line not in seen and g['sha256']==sha(line.encode()) and g['occurrences']==expected[line] and a==g['occurrences'][0],'exact text/multiplicity/representative')
  require(g['read'] is True,'unread context group');seen.add(line)
 require(set(ctx['completed_chunks'])==set(range(len(ctx['chunks']))) and len(ctx['chunks'])==26,'all bounded reading chunks')
 for r in obj(S+'/context-chunk-endings.json'):
  require(r['groups']==ctx['chunks'][r['chunk']] and r['complete'],'chunk membership')
  line=read(r['ending_path']).decode().splitlines()[r['ending_line']-1]
  require(r['ending']==line and r['ending_sha256']==sha(line.encode()),'actual chunk ending')
 coverage=[];occ={k:[] for k in obj(S+'/focused-lexical.json')['expressions']};lex=obj(S+'/focused-lexical.json')
 for p,ns in sorted(scope.items()):
  ls=read(p).decode().splitlines();ranges=[]
  for n in sorted(ns):
   if not ranges or n>ranges[-1][1]+1:ranges.append([n,n])
   else:ranges[-1][1]=n
   for key,rx in lex['expressions'].items():
    for m in re.finditer(rx,ls[n-1],re.I):occ[key].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group()})
  coverage.append({'path':p,'total_lines':len(ls),'covered_lines':len(ns),'ranges':ranges,'complete':len(ns)==len(ls),'sha256':identities[p]['sha256']})
 require(occ==lex['occurrences'] and {k:len(v) for k,v in occ.items()}==lex['counts'],'exact lexical multiset and positions')
 co=obj(S+'/completion-coverage.json');require(co['files']==coverage and co['context_line_occurrences']==sum(r['lines'] for r in ctx['files']) and co['context_unique_lines']==3342 and co['passages']==len(passages),'completion coverage exact')
 snaps=obj(S+'/snapshots.json');require({r['path'] for r in snaps if r['live_drift_allowed']}==DRIFT,'only four live drift paths')
 for r in snaps:check(r['snapshot'],r['sha256'],r['bytes'])
 # Flattened ancestor inspection: no imports or execution of their verifiers/diagnostics.
 seals=[r['path'] for r in flat if re.match(r'frontier/sources/i(?:113|116|119|122|125|128|131|134|137|140|143|146|149)_[^/]+/seal.json$',r['path'])]
 require(len(seals)==13,'ancestor seals')
 for p in seals:
  se=obj(p);ps=[r['path'] for r in se['files']];actual=set()
  for root in se['roots']:
   q=ROOT/root
   if q.is_file():actual.add(root)
   else:actual.update(str(t.relative_to(ROOT)) for t in q.rglob('*') if t.is_file())
  require(actual==set(ps)|{p},'ancestor exact membership: '+p)
  for r in se['files']:check(r['path'],r['sha256'],r['bytes'])
  require((ps!=sorted(set(ps))) if '/i125_' in p else ps==sorted(set(ps)),'original ordering verdict')
 old='frontier/sources/i149_spectral_stochastic_universality_discovery'
 require(obj(old+'/seal.json')['task_status']=='INCOMPLETE','immutable I149 remains incomplete')
 parent=obj('frontier/experiments/i149-parent-verification.json')
 require(parent['result']['task_status']=='INCOMPLETE' and parent['result']['evidence_status']=='PASS','I149 task/evidence distinction')
 receipt=obj('frontier/experiments/i125-parent-verification.json')
 require(receipt['original_replay']['exit_code']==1 and json.loads(receipt['original_replay']['stdout'])=={'error':'ValueError: canonical inventory','status':'FAIL'},'I125 literal FAIL')
 require(receipt['ordering_only_replay']['exit_code']==0 and json.loads(receipt['ordering_only_replay']['stdout'])['status']=='PASS','I125 distinct adapter PASS')
 require(obj('frontier/sources/i146_effective_boundary_exclusion/original-audit-verdicts.json')['inherited_I122_general_Lambda']=='FAIL unchanged','I122 inherited literal failure')
 require(not any(re.search(r'/(?:i|iteration)(147|148|150)[-_]',p) for p in identities),'active outputs excluded')
 for r in obj(S+'/retrievals.json'):
  if 'path' in r:check(r['path'],r['sha256'],r.get('bytes'))
  if 'existing_pdf' in r:check(r['existing_pdf'],r['sha256'],r['bytes']);require(r['matches_existing'] and r['no_copy'],'reused primary original')
  if 'text_path' in r:
   check(r['text_path'],r['text_sha256']);ls=read(r['text_path']).decode().splitlines()
   require(len(ls)==r.get('splitlines',r.get('lines')),'extraction lines')
   if 'extraction_exit' in r:require(r['extraction_exit']==0,'PDF extraction exit')
  ex=r.get('extraction')
  if isinstance(ex,dict):check(ex['path'],ex['sha256']);require(ex['exit_code']==0 and ex['command']=='pdftotext -layout','PDF extraction receipt')
 for r in obj(S+'/primary-extractions.json'):
  check(r['path'],r['sha256']);require(len(read(r['path']).decode().splitlines())==r['lines'] and r['source'] in identities,'logical HTML binding')
 for r in obj(S+'/render-log.json'):
  check(r['output'],r['output_sha256']);require(r['pdf'] in identities and r['exit']==0 and r['visually_read'],'visual formula receipt')
 disposition=obj(S+'/research-disposition.json')
 require(disposition['accepted_count']==8 and disposition['remaining_count']==2 and disposition['nomination'] is None,'no acceptance upgrade')
 require(disposition['original_I149_task_status']=='INCOMPLETE' and disposition['full_spatial_marked_process']=='PARK/unresolved','historical and mathematical limits')
 require(disposition['original_gates_complete'] and obj(S+'/progress.json')['gates_complete'],'declared gate completion')
 # Only now execute this round's new finite diagnostics, all source bytes already verified.
 phase='diagnostics';p=E+'/diagnostics.py';ns={'__name__':'i151_finite_only'}
 exec(compile(read(p),p,'exec'),ns);diagnostics=ns['run']()
 require(diagnostics['status']=='PASS','finite checks')
 rows=inventory()
 result={'evidence_status':'PASS','task_status':'COMPLETE audit and continuation; full spatial marked process PARK','original_I149_task_status':'INCOMPLETE','original_I149_evidence_status':'PASS','accepted_count':8,'remaining_count':2,'nomination':None,'preseal':preseal,'all_immutable_bytes_before_diagnostics':True,'corpus_traversals':1,'tree_entries':13223,'manuscripts':749,'original_positions':10373,'PDF_text_bindings':776,'immutable_files_read_once':len(identities),'flat_auxiliary_references':len(flat),'ancestor_seals_checked_not_executed':len(seals),'owned_files_excluding_seal':len(rows),'passages':len(passages),'context_exact_distinct_lines':3342,'context_line_occurrences':co['context_line_occurrences'],'lexical_occurrences':sum(lex['counts'].values()),'declared_recursive_semantic_reading_complete':True,'new_finite_diagnostics':diagnostics,'original_I122':'literal general-Lambda FAIL preserved','original_I125':'literal FAIL; distinct ordering-only PASS','offline':True,'read_only':True,'bytecode':False,'validated_inventory_sha256':invhash(rows),'certifies':'immutable bytes, representations, memberships, declared coverage and new finite identities only; not universal mathematics, actual semantic comprehension, contribution, acceptance, human/formal certification or the unpaid spatial identification'}
 if preseal:result['files']=rows
 else:result['seal_sha256']=identities[SEAL]['sha256']
 print(json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2))
if __name__=='__main__':
 require(sys.argv[1:] in ([],['--preseal']),'usage: verify.py [--preseal]')
 main(sys.argv[1:]==['--preseal'])
