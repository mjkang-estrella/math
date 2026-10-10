"""Read-only, offline flat replay of an explicitly INCOMPLETE research record.
No ancestor verifier/diagnostic execution; no repair or resealing path.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json,hashlib,re
from collections import Counter
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i149_spectral_stochastic_universality_discovery'
E='frontier/experiments/i149_spectral_stochastic_universality_discovery'
REPORT='frontier/iterations/i149-spectral-stochastic-universality-discovery.md'
SEAL=S+'/seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
contents={};identities={};keep=set();phase='immutable'
def require(v,m):
 if not v:raise ValueError(m)
def audit(event,args):
 if event=='open':
  mode,flags=args[1:3]
  require(not (isinstance(mode,str) and any(c in mode for c in 'wax+')),'write denied')
  require(not (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),'write flags denied')
 require(not event.startswith(('socket.','subprocess.','urllib.','http.client.')),'network/subprocess denied')
 require(event not in {'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.truncate','os.link','os.symlink','os.utime','os.exec','os.posix_spawn','os.fork'},'mutation/process denied')
sys.addaudithook(audit)
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p,retain=True):
 if p in contents:return contents[p]
 require(phase=='immutable','new bytes after immutable phase: '+p)
 require(p not in identities,'duplicate evicted read: '+p)
 q=Path(p);require(not q.is_absolute() and '..' not in q.parts,'unsafe path')
 q=ROOT/q;require(q.is_file() and not q.is_symlink(),'nonregular: '+p)
 b=q.read_bytes();identities[p]={'bytes':len(b),'sha256':sha(b),'git_sha':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
 if retain or p in keep:contents[p]=b
 return b
def obj(p):return json.loads(read(p))
def check(p,h,size=None,retain=True):
 if p not in identities:read(p,retain)
 d=identities[p];require(d['sha256']==h,'immutable hash: '+p)
 if size is not None:require(d['bytes']==size,'immutable size: '+p)
 return d
def owned():
 ps={REPORT}
 for root in (S,E):
  for p in (ROOT/root).rglob('*'):
   require(not p.is_symlink(),'owned symlink')
   if p.is_file():ps.add(str(p.relative_to(ROOT)))
 return ps
def inventory():return [{'path':p,'sha256':identities[p]['sha256'],'bytes':identities[p]['bytes']} for p in sorted(owned()-{SEAL})]
def invhash(rows):return sha(json.dumps(rows,sort_keys=True,separators=(',',':')).encode())
def decode_fields(d):return '\n'.join('FIELD '+k+'\n'+(v if isinstance(v,str) else json.dumps(v,ensure_ascii=False,indent=2)) for k,v in d.items())
def main(preseal=False):
 global phase
 if preseal:
  require(not (ROOT/SEAL).exists(),'prevalidation only before the single seal')
  for p in sorted(owned()):read(p)
 else:
  seal=obj(SEAL);require(seal['schema']=='i149-incomplete-exact-owned-v1' and seal['pin']==PIN,'seal schema/pin')
  require(seal['task_status']=='INCOMPLETE','must not upgrade incomplete task')
  require(seal['roots']==[REPORT,S+'/',E+'/'],'seal roots')
  rows=seal['files'];ps=[r['path'] for r in rows]
  require(ps==sorted(set(ps)) and set(ps)|{SEAL}==owned(),'exact canonical owned inventory')
  for r in rows:check(r['path'],r['sha256'],r['bytes'])
  require(seal['validated_inventory_sha256']==invhash(rows),'prevalidated digest')
 reads=obj(S+'/read-manifest.json')['passages'];keep.update(r['path'] for r in reads)
 flat=obj(S+'/immutable-flat.json')['files']
 require([r['path'] for r in flat]==sorted({r['path'] for r in flat}),'canonical flat inventory')
 for r in flat:check(r['path'],r['sha256'],r['bytes'])
 tree=obj('sources/preprints-tree.json');domain=obj('frontier/sources/i113_online_optimization_discovery/search-domain.json')
 require(obj('sources/upstream.json')['commit']==PIN,'upstream pin')
 require(not tree.get('truncated') and len(tree['tree'])==13223,'complete preprint tree')
 require(len({d['path'].split('/')[1] for d in tree['tree']})==749,'manuscripts')
 blobs={d['path']:d['sha'] for d in tree['tree'] if d['type']=='blob'}
 require(len(domain)==len(blobs)==10373 and {d['path'] for d in domain}==set(blobs),'complete map')
 require(Counter(d['kind'] for d in domain)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'representation counts')
 for d in domain:
  z=check(d['original_local'],d['original_sha256'],retain=False)
  require(z['git_sha']==d['git_sha']==blobs[d['path']],'pinned blob: '+d['path'])
  check(d['local'],d['sha256'],retain=False)
 actual={str(p.relative_to(ROOT)) for p in (ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus').rglob('*') if p.is_file()}
 require(actual=={d['original_local'] for d in domain if d['kind']=='corpus'},'exact corpus membership')
 require(len({d['original_local'] for d in domain})==10373,'unique originals')
 phase='representations'
 require(domain==obj('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'),'I88 map identity')
 require([{k:d[k] for k in ('path','local','kind','sha256')} for d in domain]==obj('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json'),'I79 map identity')
 requests=[json.loads(l) for l in read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').splitlines()]
 req={r['path']:r for r in requests if r.get('status')==200}
 for d in domain:
  if d['kind']=='outside_pdf':
   r=req[d['path']];ex=r['extraction']
   require(r['local']==d['original_local'] and r['sha256']==d['original_sha256'] and r['git_match'],'PDF original binding')
   require(ex['code']==0 and ex['path']==d['local'] and ex['sha256']==d['sha256'],'PDF/text binding')
 mapped={d['path']:d for d in domain}
 require(all(r==mapped[r['path']] for r in obj(S+'/selected-inventory.json')),'selected source map')
 snaps=obj(S+'/snapshots.json');require({r['live'] for r in snaps if r['drift']}==DRIFT,'only four live drift paths')
 for r in snaps:
  check(r['snapshot'],r['sha256'],r['bytes'])
  if not r['drift']:check(r['live'],r['sha256'],r['bytes'])
 contexts=obj(S+'/context-manifest.json')
 require(len(contexts)==10 and sum(r['lines'] for r in contexts)==5836,'recursive context inventory')
 require(contexts[0]['sha256']=='19d84d4dc9e9609ce93883a43aae46d44252dc601f020ea360d2daa9db312027','mandatory I146 identity')
 for r in contexts:
  check(r['path'],r['sha256'],r['bytes']);check(r['snapshot'],r['sha256'],r['bytes']);check(r['decoded'],r['decoded_sha256'])
  require(read(r['decoded']).decode()==decode_fields(obj(r['path'])),'all fields preserved in decoded representation')
  require(len(read(r['decoded']).decode().splitlines())==r['lines'],'decoded lines')
 for r in obj(S+'/originals.json'):
  check(r['path'],r['sha256'],r['bytes']);check(r['snapshot'],r['sha256'],r['bytes'])
 for r in reads:
  check(r['path'],r['sha256'],r['bytes']);ls=read(r['path']).decode().splitlines()
  require(len(ls)==r['total_lines'] and 1<=r['start']<=r['end']<=len(ls),'actual passage range')
  require(r['ending']==ls[r['end']-1] and r['passage_sha256']==sha('\n'.join(ls[r['start']-1:r['end']]).encode()),'passage ending/hash')
  if 'pinned_url' in r:require(r['pinned_url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/preprints/'+r['path'].split('/corpus/preprints/')[1],'pinned URL')
 lex=obj(S+'/focused-lexical.json');found={k:[] for k in lex['expressions']};scope={}
 for r in reads:scope.setdefault(r['path'],set()).update(range(r['start'],r['end']+1))
 for p,ns in sorted(scope.items()):
  ls=read(p).decode().splitlines()
  for n in sorted(ns):
   for k,rx in lex['expressions'].items():
    for m in re.finditer(rx,ls[n-1],re.I):found[k].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group(),'text':ls[n-1]})
 require(found==lex['occurrences'] and {k:len(v) for k,v in found.items()}==lex['counts'],'exact lexical multiset/positions')
 limits=obj(S+'/reading-limitations.json');require(limits['all_decoded_fields_mandatory_I146'] and not limits['all_recursive_decoded_fields'],'semantic coverage cannot be promoted')
 for r in contexts[:2]:require(scope.get(r['decoded'])==set(range(1,r['lines']+1)),'completed context declared coverage')
 # One flat inspection of inherited seals and receipts, never executing their code.
 seals=[r['path'] for r in flat if re.match(r'frontier/sources/i(?:113|116|119|122|125|128|131|134|137|140|143|146)_[^/]+/seal.json$',r['path'])]
 require(len(seals)==12,'flat ancestor seal count')
 for p in seals:
  se=obj(p);ps=[r['path'] for r in se['files']];actual=set()
  for root in se['roots']:
   q=ROOT/root
   if q.is_file():actual.add(root)
   else:actual.update(str(t.relative_to(ROOT)) for t in q.rglob('*') if t.is_file())
  require(actual==set(ps)|{p},'ancestor exact membership')
  for r in se['files']:check(r['path'],r['sha256'],r['bytes'])
  require((ps!=sorted(set(ps))) if '/i125_' in p else (ps==sorted(set(ps))),'literal ancestor ordering verdict')
 receipt=obj('frontier/experiments/i125-parent-verification.json')
 require(receipt['original_replay']['exit_code']==1 and json.loads(receipt['original_replay']['stdout'])=={'error':'ValueError: canonical inventory','status':'FAIL'},'original I125 literal FAIL')
 require(receipt['ordering_only_replay']['exit_code']==0 and json.loads(receipt['ordering_only_replay']['stdout'])['status']=='PASS','distinct I125 adapter PASS')
 require('FAIL' in read('frontier/sources/i146_effective_boundary_exclusion/original-audit-verdicts.json').decode(),'inherited literal failures preserved')
 require(not any(re.search(r'/(?:i|iteration)(147|148)[-_]',p) for p in identities),'active outputs excluded')
 for r in obj(S+'/retrievals.json'):
  if r.get('status')==200:
   check(r['path'],r['sha256'],r['bytes'])
   if 'text_path' in r:
    check(r['text_path'],r['text_sha256'],r['text_bytes'])
    require(r['extraction_exit']==0 and r['extraction_command'][:2]==['pdftotext','-layout'],'new extraction receipt, no re-extraction')
    require(len(read(r['text_path']).decode().splitlines())==r['splitlines'],'new PDF text lines')
 require(obj(S+'/research-disposition.json')['task_status']=='INCOMPLETE' and obj(S+'/research-disposition.json')['nomination'] is None,'no task/acceptance upgrade')
 phase='diagnostics'
 p=E+'/diagnostics.py';ns={'__name__':'i149_new_finite_only'};exec(compile(read(p),p,'exec'),ns);diagnostics=ns['run']()
 require(diagnostics==obj(E+'/diagnostics.json'),'new diagnostics record')
 rows=inventory()
 result={'evidence_status':'PASS','task_status':'INCOMPLETE','accepted_count':8,'nomination':None,'preseal':preseal,
 'all_immutable_bytes_before_diagnostics':True,'corpus_traversals':1,'tree_entries':13223,'manuscripts':749,'original_positions':10373,'PDF_text_bindings':776,
 'immutable_files_read_once':len(identities),'flat_auxiliary_references':len(flat),'ancestor_seals_checked_not_executed':len(seals),
 'owned_files_excluding_seal':len(rows),'passages':len(reads),'lexical_occurrences':sum(lex['counts'].values()),
 'mandatory_I146_all_decoded_fields':True,'all_recursive_semantic_reading':False,'new_finite_diagnostics':diagnostics,
 'original_I125':'literal FAIL preserved; distinct ordering-only PASS preserved','original_I122':'literal general-Lambda FAIL preserved',
 'offline':True,'read_only':True,'validated_inventory_sha256':invhash(rows),
 'certifies':'immutable bytes, memberships, representations and finite identities only; no completion of missing reading, full audit, universal mathematics, contribution or acceptance'}
 if not preseal:result['seal_sha256']=identities[SEAL]['sha256']
 print(json.dumps(result,sort_keys=True,indent=2))
if __name__=='__main__':
 require(sys.argv[1:] in ([],['--preseal']),'usage: verify.py [--preseal]')
 main(sys.argv[1:]==['--preseal'])
