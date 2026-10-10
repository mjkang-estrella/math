"""Offline, read-only flat evidence verification. No ancestor verifier execution.
All immutable bytes are checked before representation checks or new diagnostics.
No network, subprocess, writes, bytecode, repair, extraction tool, or resealing.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re,runpy,os
from collections import Counter
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i146_effective_boundary_exclusion'
E='frontier/experiments/i146_effective_boundary_exclusion'
REPORT='frontier/iterations/i146-effective-boundary-exclusion.md'
SEAL=S+'/seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
DOMAIN='frontier/sources/i113_online_optimization_discovery/search-domain.json'
contents={};identities={};keep=set();phase='immutable'
def require(v,m):
 if not v:raise ValueError(m)
def audit(event,args):
 if event=='open':
  mode=args[1];flags=args[2]
  require(not (isinstance(mode,str) and any(c in mode for c in 'wax+')),'write denied')
  require(not (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),'write flags denied')
 require(not event.startswith(('socket.','subprocess.','urllib.','http.client.')),'network/subprocess denied')
 require(event not in {'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.truncate','os.link','os.symlink','os.utime','os.exec','os.posix_spawn','os.fork'},'mutation/process denied')
sys.addaudithook(audit)
def sha(b):return hashlib.sha256(b).hexdigest()
def path(p):
 q=Path(p);require(not q.is_absolute() and '..' not in q.parts,'unsafe path')
 q=ROOT/q;require(q.is_file() and not q.is_symlink(),'missing/nonregular: '+p);return q
def read(p,retain=True):
 if p in contents:return contents[p]
 require(phase=='immutable','new immutable read after byte phase: '+p)
 require(p not in identities,'would reread evicted immutable bytes: '+p)
 b=path(p).read_bytes()
 identities[p]={'sha256':sha(b),'bytes':len(b),'git_sha':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
 if retain or p in keep:contents[p]=b
 return b
def obj(p):return json.loads(read(p))
def check(p,h,size=None,retain=True):
 if p not in identities:read(p,retain)
 d=identities[p];require(d['sha256']==h,'immutable SHA-256: '+p)
 if size is not None:require(d['bytes']==size,'immutable size: '+p)
 return d
def owned():
 out={REPORT}
 for base in (S,E):
  for p in (ROOT/base).rglob('*'):
   require(not p.is_symlink(),'owned symlink')
   if p.is_file():out.add(str(p.relative_to(ROOT)))
 return out
def inventory():return [{'path':p,**{k:identities[p][k] for k in ('bytes','sha256')}} for p in sorted(owned()-{SEAL})]
def invhash(rows):return sha(json.dumps(rows,sort_keys=True,separators=(',',':')).encode())
def decode_fields(d):return '\n'.join('FIELD '+k+'\n'+(v if isinstance(v,str) else json.dumps(v,ensure_ascii=False,indent=2)) for k,v in d.items())
def main(preseal=False):
 global phase
 require(not preseal or not (ROOT/SEAL).exists(),'preseal requires absent final seal')
 if not preseal:
  seal=obj(SEAL);require(seal['schema']=='i146-exact-owned-v1' and seal['pin']==PIN,'seal contract')
  require(seal['roots']==[REPORT,S+'/',E+'/'],'seal roots')
  rows=seal['files'];ps=[d['path'] for d in rows]
  require(ps==sorted(set(ps)),'canonical globally sorted inventory')
  require(set(ps)|{SEAL}==owned() and SEAL not in ps,'exact owned membership')
  for d in rows:check(d['path'],d['sha256'],d['bytes'])
  require(seal['validated_inventory_sha256']==invhash(rows),'validated inventory digest')
 else:
  for p in sorted(owned()):read(p)
 flat=obj(S+'/immutable-flat.json')['files']
 require([r['path'] for r in flat]==sorted({r['path'] for r in flat}),'canonical flat refs')
 for r in flat:check(r['path'],r['sha256'],r['bytes'])
 require(obj('sources/upstream.json')['commit']==PIN,'upstream pin')
 reads=obj(S+'/read-manifest.json')['passages'];keep.update(r['path'] for r in reads)
 domain=obj(DOMAIN);tree=obj('sources/preprints-tree.json');blobs={d['path']:d['sha'] for d in tree['tree'] if d['type']=='blob'}
 require(not tree.get('truncated',False) and len(tree['tree'])==13223,'complete tree')
 require(len({d['path'].split('/')[1] for d in tree['tree']})==749,'manuscript count')
 require(len(domain)==len(blobs)==10373 and {d['path'] for d in domain}==set(blobs),'complete original mapping')
 require(Counter(d['kind'] for d in domain)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'representation counts')
 for d in domain:
  z=check(d['original_local'],d['original_sha256'],retain=False)
  require(z['git_sha']==d['git_sha']==blobs[d['path']],'pinned Git identity: '+d['path'])
  check(d['local'],d['sha256'],retain=False)
 require(len({d['original_local'] for d in domain})==10373,'unique originals')
 actual={str(p.relative_to(ROOT)) for p in (ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus').rglob('*') if p.is_file()}
 require(actual=={d['original_local'] for d in domain if d['kind']=='corpus'},'exact inherited corpus membership')
 # Every owned/referenced immutable byte has now been checked. Only four live ledgers may drift.
 phase='representations'
 require(domain==obj('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'),'I88 complete mapping identity')
 require([{k:d[k] for k in ('path','local','kind','sha256')} for d in domain]==obj('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json'),'I79 representation mapping')
 requests=[json.loads(l) for l in read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').splitlines()]
 req={d['path']:d for d in requests if d.get('status')==200}
 for d in domain:
  if d['kind']=='outside_pdf':
   r=req[d['path']];ex=r['extraction']
   require(r['local']==d['original_local'] and r['sha256']==d['original_sha256'] and r['git_match'],'PDF original binding')
   require(ex['code']==0 and ex['path']==d['local'] and ex['sha256']==d['sha256'],'PDF/text extraction binding')
 mapped={r['path']:r for r in domain}
 require(all(d==mapped[d['path']] for d in obj(S+'/selected-inventory.json')),'selected mapping')
 snaps=obj(S+'/snapshots.json')
 require({d['live'] for d in snaps if d['drift']}==DRIFT,'only four live ledgers may drift')
 for d in snaps:
  check(d['snapshot'],d['sha256'],d['bytes'])
  if not d['drift']:check(d['live'],d['sha256'],d['bytes'])
 for r in obj(S+'/context-manifest.json'):
  check(r['path'],r['sha256']);require(read(r['decoded']).decode()==decode_fields(obj(r['path'])),'all decoded fields')
 require(obj(S+'/context-manifest.json')[0]['sha256']=='cd007ff0fb20c881443cdd1130ed094eda4861f1a94e806637fa538f73da45a1','mandatory original task hash')
 for r in reads:
  check(r['path'],r['sha256'],r['bytes']);ls=read(r['path']).decode(errors='replace').splitlines()
  require(len(ls)==r['total_lines'] and 1<=r['start']<=r['end']<=len(ls),'reading range')
  require(sha('\n'.join(ls[r['start']-1:r['end']]).encode())==r['passage_sha256'] and ls[r['end']-1]==r['ending'],'actual passage/ending')
  if 'pinned_url' in r:require(r['pinned_url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/preprints/'+r['path'].split('/corpus/preprints/',1)[1],'pinned read URL')
 lex=obj(S+'/focused-lexical.json');found={k:[] for k in lex['expressions']};lscope={}
 for r in reads:
  lscope.setdefault(r['path'],set()).update(range(r['start'],r['end']+1))
 for p,ns in sorted(lscope.items()):
  ls=read(p).decode().splitlines()
  for n in sorted(ns):
   for name,expr in lex['expressions'].items():
    for m in re.finditer(expr,ls[n-1],re.I):found[name].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group(),'text':ls[n-1]})
 require(found==lex['occurrences'] and {k:len(v) for k,v in found.items()}==lex['counts'],'exact lexical positions and multiplicities')
 # The extractor is imported only after its immutable bytes and every input byte are checked.
 extractor_path='frontier/experiments/i131_soft_summary_stability/extract_html.py';ns={'__name__':'i146_readonly_html'}
 exec(compile(read(extractor_path),extractor_path,'exec'),ns);extractor=ns['extract']
 ext=obj(S+'/retrievals.json');require(len(ext)==3,'three current arXiv raw retrievals')
 successes=[d for d in ext if d.get('status')==200]
 require(len(successes)==3,'current arXiv retrievals; separate DOI failure preserved')
 for d in successes:
  check(d['path'],d['sha256'],d['bytes']);check(d['text_path'],d['text_sha256'])
  if d['path'].endswith('.html'):require(extractor(read(d['path']).decode())==read(d['text_path']).decode(),'HTML exact representation')
  else:require(d['extraction_exit']==0 and d['extraction_command'][0:2]==['pdftotext','-layout'],'PDF extraction binding; not re-extracted')
  require(len(read(d['text_path']).decode().splitlines())==d['splitlines'],'representation lines')
 # Check ancestor exact owned memberships without running any ancestor verifier.
 ancestor_seals=[r['path'] for r in flat if re.match(r'frontier/sources/i(?:113|116|119|122|125|128|131|134|137|140|143)_[^/]+/seal.json$',r['path'])]
 require(len(ancestor_seals)==11,'one flat ancestor chain')
 for p in ancestor_seals:
  se=obj(p);listed=[r['path'] for r in se['files']];actual=set()
  for root in se['roots']:
   q=ROOT/root
   if q.is_file():actual.add(root)
   else:actual.update(str(t.relative_to(ROOT)) for t in q.rglob('*') if t.is_file())
  require(actual==set(listed)|{p},'ancestor exact membership: '+p)
  for r in se['files']:check(r['path'],r['sha256'],r['bytes'])
  if '/i125_' in p:require(listed!=sorted(set(listed)),'preserve original I125 ordering failure')
  else:require(listed==sorted(set(listed)),'ancestor canonical inventory')
 parent125=obj('frontier/experiments/i125-parent-verification.json')
 require(parent125['original_replay']['exit_code']==1 and json.loads(parent125['original_replay']['stdout'])=={'error':'ValueError: canonical inventory','status':'FAIL'},'I125 original FAIL receipt')
 require(parent125['ordering_only_replay']['exit_code']==0 and json.loads(parent125['ordering_only_replay']['stdout'])['status']=='PASS','distinct parent adapter PASS receipt')
 check('frontier/experiments/i125-parent-order-replay.py','0507da4a890521e3d8e2b875bd8720c8c3e5ebf6093879fc134ee1178a65227e')
 inherited_diagnostics=[r['path'] for r in flat if re.match(r'frontier/experiments/i(?:113|116|119|122|125|128|131|134|137|140|143)_[^/]+/diagnostics.json$',r['path'])]
 require(len(inherited_diagnostics)==11,'inherited diagnostic record count')
 for p in inherited_diagnostics:require(obj(p)['status']=='PASS','frozen inherited diagnostic status')
 require('FAIL' in read(S+'/original-audit-verdicts.json').decode(),'inherited failures recorded')
 cr=obj(S+'/context-reading.json');require(cr['all_decoded_fields'],'complete context gate')
 for r in cr['records']:
  check(r['decoded'],r['decoded_sha256']);check(r['snapshot'],r['sha256'],r['bytes'])
  require(read(r['snapshot'])==read(r['path']),'frozen original task bytes')
  require(r['lines']==len(read(r['decoded']).decode().splitlines()),'full context line count')
  covered=set()
  for d in reads:
   if d['path']==r['decoded']:covered.update(range(d['start'],d['end']+1))
  require(covered==set(range(1,r['lines']+1)),'every decoded original line read')
 for r in obj(S+'/originals.json'):
  check(r['path'],r['sha256'],r['bytes']);check(r['snapshot'],r['sha256'],r['bytes'])
 require(not any(re.search(r'/(?:i|iteration)(141|142|144|145)',p) for p in identities),'active outputs excluded')
 require(obj('frontier/experiments/i143-parent-verification.json')['exit_code']==0,'immutable selective I143 parent receipt')
 require(obj(S+'/research-disposition.json')['nomination'] is None,'no nomination')
 require(sum(r['lines'] for r in cr['records'])==5320,'all recursive decoded context')
 require(len(cr['records'])==9,'nine full decoded records')
 phase='diagnostics'
 diag_path=E+'/diagnostics.py';ns={'__name__':'i146_new_finite_only'}
 exec(compile(read(diag_path),diag_path,'exec'),ns);new=ns['run']()
 require(new==obj(E+'/diagnostics.json'),'new finite diagnostics replay')
 rows=inventory();result={'status':'PASS','preseal':preseal,'accepted_count':8,'nomination':None,'qualitative_target_L':'technical bound','effective_numerical_K0':'PARK','effective_boundary_exclusion':'PARK','original_I143_paid_audit':'PASS without repairs at stated scopes','global_S128':'PARK; unproved/unrefuted','offline':True,'read_only':True,'all_immutable_bytes_before_diagnostics':True,'corpus_replays':1,'corpus':{'tree_entries':13223,'manuscripts':749,'original_positions':10373,'i14_originals':9340,'additional_originals':1033,'inherited_pdf_texts':776},'flat_auxiliary_references':len(flat),'immutable_files_read_once':len(identities),'owned_files_excluding_seal':len(rows),'passages':len(reads),'source_lexical_occurrences':sum(lex['counts'].values()),'inherited_diagnostic_records_verified_not_executed':len(inherited_diagnostics),'new_finite_diagnostics':new,'original_I125_verifier':'FAIL: canonical inventory, preserved','I125_ordering_only_adapter':'distinct PASS receipt; unchanged adapter; not rerun','original_I122_general_Lambda_equality':'FAIL preserved','live_ledger_drift_allowlist':sorted(DRIFT),'validated_inventory_sha256':invhash(rows),'certifies':'immutable bytes, memberships, representations and finite identities only; not universal mathematics, novelty, external certificates or acceptance'}
 if not preseal:result['seal_sha256']=identities[SEAL]['sha256']
 print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':
 require(sys.argv[1:] in ([],['--preseal']),'usage: verify.py [--preseal]')
 main(sys.argv[1:]==['--preseal'])
