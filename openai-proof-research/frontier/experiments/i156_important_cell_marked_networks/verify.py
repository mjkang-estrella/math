"""I156 offline read-only replay. No ancestor code, converter, repair or reseal.
Every immutable binding is checked before executing the new finite diagnostics.
--preseal validates the exact candidate inventory before the one external seal.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json,hashlib,re
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i156_important_cell_marked_networks'
E='frontier/experiments/i156_important_cell_marked_networks'
OLD='frontier/sources/i151_spatial_dynamical_percolation_continuation'
REPORT='frontier/iterations/i156-important-cell-marked-networks.md'
SEAL=S+'/seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
cache={};identities={};phase='immutable'
def need(v,m):
 if not v:raise ValueError(m)
def guard(event,args):
 if event=='open':
  mode,flags=args[1:3]
  need(not(isinstance(mode,str) and any(c in mode for c in 'wax+')),'writes denied')
  need(not(isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),'write flags denied')
 need(not event.startswith(('socket.','subprocess.','urllib.','http.client.','ctypes.')),'network/process/native escape denied')
 need(event not in {'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.truncate','os.link','os.symlink','os.utime','os.exec','os.posix_spawn','os.fork','os.forkpty','os.putenv','os.unsetenv'},'mutation/process denied')
sys.addaudithook(guard)
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p,retain=True):
 if p in cache:return cache[p]
 need(phase=='immutable','unloaded bytes after immutable phase: '+p)
 need(p not in identities,'duplicate evicted read: '+p)
 q=Path(p);need(not q.is_absolute() and '..' not in q.parts,'unsafe path')
 q=ROOT/q;need(q.is_file() and not q.is_symlink(),'nonregular path: '+p)
 b=q.read_bytes();identities[p]={'bytes':len(b),'sha256':sha(b),'git_sha':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
 if retain:cache[p]=b
 return b
def obj(p):return json.loads(read(p))
def check(p,h,size=None,retain=True):
 if p not in identities:read(p,retain)
 d=identities[p];need(d['sha256']==h,'immutable hash: '+p)
 if size is not None:need(d['bytes']==size,'immutable size: '+p)
 return d
def owned():
 ps={REPORT}
 for r in (S,E):
  for p in (ROOT/r).rglob('*'):
   need(not p.is_symlink(),'owned symlink')
   if p.is_file():ps.add(str(p.relative_to(ROOT)))
 return ps
def invhash(rows):return sha(json.dumps(rows,sort_keys=True,separators=(',',':')).encode())
def decode(d):return '\n'.join('FIELD '+k+'\n'+(v if isinstance(v,str) else json.dumps(v,ensure_ascii=False,indent=2)) for k,v in d.items())
def main(preseal):
 global phase
 if preseal:
  need(not (ROOT/SEAL).exists(),'prevalidation only before seal')
  for p in sorted(owned()):read(p)
 else:
  se=obj(SEAL);need(se['schema']=='i156-exact-owned-v1' and se['pin']==PIN,'schema/pin')
  need(se['roots']==[REPORT,S+'/',E+'/'],'owned roots')
  rows=se['files'];ps=[r['path'] for r in rows]
  need(ps==sorted(set(ps)) and set(ps)|{SEAL}==owned(),'canonical exact owned inventory')
  for r in rows:check(r['path'],r['sha256'],r['bytes'])
  need(invhash(rows)==se['validated_inventory_sha256'],'prevalidated inventory')
 flat=obj(S+'/immutable-flat.json')['files']
 need([r['path'] for r in flat]==sorted({r['path'] for r in flat}),'canonical flat inventory')
 need(not any(r['path'] in DRIFT for r in flat),'live ledgers must be snapshots')
 for r in flat:check(r['path'],r['sha256'],r['bytes'])
 tree=obj('sources/preprints-tree.json');domain=obj('frontier/sources/i113_online_optimization_discovery/search-domain.json')
 need(obj('sources/upstream.json')['commit']==PIN,'pinned premise')
 need(not tree.get('truncated') and len(tree['tree'])==13223,'complete tree')
 need(len({r['path'].split('/')[1] for r in tree['tree']})==749,'749 manuscripts')
 blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
 need(len(domain)==len(blobs)==10373 and {r['path'] for r in domain}==set(blobs),'complete original map')
 need(Counter(r['kind'] for r in domain)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'map kinds')
 # One flat traversal; duplicate references reuse identities rather than reread bytes.
 for r in domain:
  d=check(r['original_local'],r['original_sha256'],retain=False)
  need(d['git_sha']==r['git_sha']==blobs[r['path']],'pinned git object: '+r['path'])
  check(r['local'],r['sha256'],retain=False)
 actual={str(p.relative_to(ROOT)) for p in (ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus').rglob('*') if p.is_file()}
 need(actual=={r['original_local'] for r in domain if r['kind']=='corpus'},'exact corpus membership')
 need(len({r['original_local'] for r in domain})==10373,'unique original bindings')
 # All ancestral bytes and exact memberships, without importing or running their code.
 seals=[r['path'] for r in flat if re.match(r'frontier/sources/i(?:113|116|119|122|125|128|131|134|137|140|143|146|149|151)_[^/]+/seal.json$',r['path'])]
 need(len(seals)==14,'fourteen ancestor seals')
 for p in seals:
  se=obj(p);paths=[r['path'] for r in se['files']];actual=set()
  for root in se['roots']:
   q=ROOT/root
   if q.is_file():actual.add(root)
   else:actual.update(str(t.relative_to(ROOT)) for t in q.rglob('*') if t.is_file())
  need(actual==set(paths)|{p},'ancestor exact membership: '+p)
  for r in se['files']:
   need(r['path'] in identities,'nonflat ancestor binding: '+r['path'])
   check(r['path'],r['sha256'],r['bytes'])
  need((paths!=sorted(set(paths))) if '/i125_' in p else paths==sorted(set(paths)),'historical ordering result')
 need(not any(re.search(r'/(?:i|iteration)(154|155)[-_]',p) for p in identities),'no active project binding')
 phase='representations'
 need(domain==obj('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'),'I88 identical flat map')
 need([{k:r[k] for k in ('path','local','kind','sha256')} for r in domain]==obj('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json'),'I79 identical projection')
 req={r['path']:r for r in map(json.loads,read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').splitlines()) if r.get('status')==200}
 for r in domain:
  if r['kind']=='outside_pdf':
   a=req[r['path']];b=a['extraction']
   need(a['local']==r['original_local'] and a['sha256']==r['original_sha256'] and a['git_match'],'PDF source binding')
   need(b['code']==0 and b['path']==r['local'] and b['sha256']==r['sha256'],'PDF text binding')
 task='frontier/iterations/iteration151-spatial-dynamical-percolation-continuation-task.json'
 need(identities[task]['sha256']=='464f4585fd078eced8cd8ac1857713ef1fea9195d264e952bb2cbc2979a96dbd','mandatory original I151')
 need(read(S+'/original-i151.decoded.txt').decode()==decode(obj(task)),'all original I151 fields')
 p=obj(S+'/progress.json');ctx=obj(OLD+'/context-reading-plan.json');scope={};readlines=set()
 for r in p['read_passages']:
  check(r['path'],r['sha256']);ls=read(r['path']).decode().splitlines()
  need(r['displayed'] and len(ls)==r['total_lines'] and 1<=r['start']<=r['end']<=len(ls),'actual reading range')
  need(ls[r['end']-1]==r['ending'] and sha('\n'.join(ls[r['start']-1:r['end']]).encode())==r['passage_sha256'],'reading ending/hash')
  scope.setdefault(r['path'],set()).update(range(r['start'],r['end']+1));readlines.update(ls[r['start']-1:r['end']])
 expected={}
 for r in ctx['files']:
  check(r['path'],r['sha256']);ls=read(r['path']).decode().splitlines();need(len(ls)==r['lines'],'context line count')
  scope.setdefault(r['path'],set()).update(range(1,len(ls)+1))
  for n,line in enumerate(ls,1):expected.setdefault(line,[]).append({'path':r['path'],'line':n})
  if r['path'].endswith('.decoded.txt'):
   raw=r['path'].replace('.decoded.txt','.json')
   need(read(r['path']).decode()==decode(obj(raw)),'recursive all decoded fields')
   need(read(raw)==read('frontier/iterations/'+Path(raw).name),'original recursive snapshot')
 covered=set(p['context_extra_read']);reused=[];seen=set()
 for i in p['context_chunks_read']:covered.update(ctx['chunks'][i])
 for i,g in enumerate(ctx['groups']):
  a=g['representative'];line=read(a['path']).decode().splitlines()[a['line']-1]
  need(line not in seen and g['sha256']==sha(line.encode()) and g['occurrences']==expected[line] and a==g['occurrences'][0],'exact context multiset/positions')
  seen.add(line)
  if i not in covered and line in readlines:covered.add(i);reused.append(i)
 need(len(seen)==3342 and covered==set(range(3342)) and reused==p['context_exact_reuse_groups'],'declared complete distinct-line coverage')
 need(set(range(744,802))|{1483}<=set(p['recovered_context_groups']),'truncated context recovered')
 need(p['original_reading_complete'],'declared recursive gate')
 lex=obj(S+'/lexical.json');occ={k:[] for k in lex['expressions']};coverage=[]
 for path,ns in sorted(scope.items()):
  ls=read(path).decode().splitlines();ranges=[]
  for n in sorted(ns):
   if not ranges or n>ranges[-1][1]+1:ranges.append([n,n])
   else:ranges[-1][1]=n
   for k,rx in lex['expressions'].items():
    for m in re.finditer(rx,ls[n-1],re.I):occ[k].append({'path':path,'line':n,'start':m.start(),'end':m.end(),'match':m.group()})
  coverage.append({'path':path,'sha256':identities[path]['sha256'],'ranges':ranges,'covered_lines':len(ns),'total_lines':len(ls),'complete':len(ns)==len(ls),'ending':ls[max(ns)-1]})
 co=obj(S+'/reading-coverage.json');need(co['files']==coverage and co['passages']==len(p['read_passages']),'exact current coverage')
 need(co['context_line_occurrences']==sum(r['lines'] for r in ctx['files'])==13094,'context occurrence count')
 need(occ==lex['occurrences'] and {k:len(v) for k,v in occ.items()}==lex['counts'],'lexical exact multisets and positions')
 # Complete declared source operations; historical larger gates remain historical.
 for path,ns in scope.items():
  if '/From-critical-crossings-' in path or '/A-Pivotal-Amplitude-' in path:
   need(ns==set(range(1,len(read(path).decode().splitlines())+1)),'declared full operation ending')
 snaps=obj(S+'/snapshots.json');need({r['live_path'] for r in snaps}==DRIFT,'only four allowed live drifts')
 for r in snaps:check(r['snapshot'],r['sha256'],r['bytes'])
 old='frontier/sources/i149_spectral_stochastic_universality_discovery'
 need(obj(old+'/seal.json')['task_status']=='INCOMPLETE','historical I149 task')
 receipt=obj('frontier/experiments/i149-parent-verification.json')['result']
 need(receipt['task_status']=='INCOMPLETE' and receipt['evidence_status']=='PASS','historical task/evidence distinction')
 receipt=obj('frontier/experiments/i125-parent-verification.json')
 need(receipt['original_replay']['exit_code']==1 and json.loads(receipt['original_replay']['stdout'])=={'error':'ValueError: canonical inventory','status':'FAIL'},'literal I125 FAIL')
 need(receipt['ordering_only_replay']['exit_code']==0 and json.loads(receipt['ordering_only_replay']['stdout'])['status']=='PASS','distinct I125 adapter')
 need(obj('frontier/sources/i146_effective_boundary_exclusion/original-audit-verdicts.json')['inherited_I122_general_Lambda']=='FAIL unchanged','literal I122 FAIL')
 parent=obj('frontier/experiments/i151-parent-verification.json')
 need(json.loads(parent['stdout'])==parent['result'] and parent['result']['evidence_status']=='PASS','I151 finalized receipt consistency')
 need(parent['seal_sha256']==identities[OLD+'/seal.json']['sha256']=='cb0a4c9fce3e396cc3c332dc9de792e3da7c0ecbbc207b555bc5cf7a8229cc5c','unchanged original seal')
 d=obj(S+'/disposition.json');need(d['accepted_count']==8 and d['remaining_count']==2 and d['nomination'] is None and d['target']=='PARK/unresolved','no acceptance or target upgrade')
 phase='diagnostics'
 ns={'__name__':'i156_new_finite_only'};path=E+'/diagnostics.py'
 exec(compile(read(path),path,'exec'),ns);diag=ns['run']();need(diag['status']=='PASS','new finite checks')
 rows=[{'path':p,'sha256':identities[p]['sha256'],'bytes':identities[p]['bytes']} for p in sorted(owned()-{SEAL})]
 result={'evidence_status':'PASS','task_status':d['task_scope'],'full_target':'PARK/unresolved','original_exact_inclusion':'FAIL','original_overlap_extraction':'unresolved as exhibited; separate extension proved','accepted_count':8,'remaining_count':2,'nomination':None,'preseal':preseal,'offline':True,'read_only':True,'bytecode':False,'all_immutable_bytes_before_diagnostics':True,'corpus_traversals':1,'tree_entries':13223,'manuscripts':749,'original_positions':10373,'PDF_text_bindings':776,'immutable_files_read_once':len(identities),'ancestor_seals_checked_not_executed':len(seals),'flat_references':len(flat),'context_distinct_lines':3342,'context_line_occurrences':13094,'passages':len(p['read_passages']) if isinstance(p,dict) else len(obj(S+'/progress.json')['read_passages']),'lexical_occurrences':sum(lex['counts'].values()),'owned_files_excluding_seal':len(rows),'validated_inventory_sha256':invhash(rows),'new_finite_diagnostics':diag,'certifies':'immutable bytes, memberships, representations, declared coverage, lexical positions and finite identities only; not universal mathematics, semantic comprehension, substantiality, acceptance or the unresolved network theorem'}
 if preseal:result['files']=rows
 else:result['seal_sha256']=identities[SEAL]['sha256']
 print(json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2))
if __name__=='__main__':
 need(sys.argv[1:] in ([],['--preseal']),'usage: verify.py [--preseal]')
 main(sys.argv[1:]==['--preseal'])
