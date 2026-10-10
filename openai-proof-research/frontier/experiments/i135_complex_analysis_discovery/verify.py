"""Offline read-only immutable-prefix replay, followed only by new finite diagnostics."""
import sys
sys.dont_write_bytecode=True
import os

def readonly(event,args):
 if event=='open':
  mode=args[1];flags=args[2] if len(args)>2 else 0
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
   raise RuntimeError('Read-only replay blocked write '+repr(args[0]))
 if event.startswith(('socket.','subprocess.')) or event in {'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.utime','os.truncate','os.link','os.symlink','shutil.copyfile','os.putenv','os.unsetenv','os.exec','os.posix_spawn'}:
  raise RuntimeError('Offline read-only replay blocked '+event)
sys.addaudithook(readonly)
import ast,hashlib,json,re,runpy
from pathlib import Path
ROOT=Path.cwd().resolve()
S=Path('frontier/sources/i135_complex_analysis_discovery');X=Path('frontier/experiments/i135_complex_analysis_discovery');R=Path('frontier/iterations/i135-complex-analysis-discovery.md')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TASKS={120:('thermal-trace-stability','d1b09ad8939c4842ddba3c672336e31f52ea6b0ec0433ac6e0ace2cbacad292d'),123:('thermal-production-stability','c0a4216b88cf7bde8e7ff4517c0d4fb2144e5457d1ab57fc5315f1d739653172'),126:('random-geometry-discovery','38e2d007ce9cb236a9601392a586e72263279bdc28744e394d8997cd457f6651'),129:('disordered-fk-occupation','96547471b969b143cc84a80c6efdc12897315973c2ab322c4ae5ee18cbdd9147'),132:('discrete-probability-discovery','72aa941eb08f8b305ce8a3f9eb35ce8ebda5bcf929f49a84f34211d3cb91c4e7')}
def require(ok,msg):
 if not ok:raise AssertionError(msg)
def read(p):
 p=Path(p);require(p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(ROOT),'Missing/symlink/outside '+str(p));return p.read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(read(p))
def row(p):b=read(p);return dict(path=str(p),sha256=sha(b),bytes=len(b))
def inactive(p):require(not re.search(r'(?:^|/)(?:i|iteration)(?:133|134|136)(?:[-_/])',p),'Active output dependency '+p)
def inventory():
 files=[str(R)];dirs=[]
 for root in (S,X):
  require(root.is_dir() and not root.is_symlink(),'Owned root');dirs.append(str(root))
  for p in root.rglob('*'):
   require(not p.is_symlink(),'Owned symlink')
   if p.is_dir():dirs.append(str(p))
   elif p.is_file() and p!=S/'seal.json':files.append(str(p))
   elif p!=S/'seal.json':require(False,'Unexpected filesystem object')
 require(len(files)==len(set(files)) and len(dirs)==len(set(dirs)),'Duplicate inventory')
 return sorted(files),sorted(dirs)

def immutable_prefix(path,digest,boundary,ret):
 source=read(path);require(sha(source)==digest,'Pinned original verifier '+path)
 tree=ast.parse(source,filename=path);mains=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main'];require(len(mains)==1,'Unique original main');main=mains[0]
 cuts=[i for i,n in enumerate(main.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==boundary for t in n.targets)]
 require(len(cuts)==1,'Unique immutable-prefix boundary '+boundary)
 main.body=main.body[:cuts[0]]+ast.parse(ret).body
 require(isinstance(tree.body[-1],ast.If),'Original entry point');tree.body.pop();ast.fix_missing_locations(tree)
 ns={'__name__':'i135_immutable_adapter','__file__':path};exec(compile(tree,path+' [immutable prefix only]','exec'),ns)
 saved=sys.argv;sys.argv=[path]
 try:return ns['main']()
 finally:sys.argv=saved

def main():
 require(sys.argv[1:] in ([],['--preseal']),'Only --preseal supported');pre=bool(sys.argv[1:]);files,dirs=inventory()
 validated=[row(p) for p in files if p!=str(S/'preseal-validation.json')]
 if pre:require(not (S/'seal.json').exists(),'Preseal refuses sealed package')
 else:
  seal=load(S/'seal.json');require(seal['schema']=='i135-one-final-seal-v1' and seal['globally_sorted_exact_inventory'] is True,'Seal identity')
  require(seal['files']==[row(p) for p in files] and seal['directories']==dirs,'All owned immutable bytes and globally sorted exact inventory')
  receipt=load(S/'preseal-validation.json');require(receipt['status']=='PASS' and receipt['validated_files']==validated,'Preseal final bytes')
 refs=load(S/'references.json');require([r['path'] for r in refs]==sorted(set(r['path'] for r in refs)),'Reference order')
 for r in refs:inactive(r['path']);require(r['path'] not in MUTABLE and row(r['path'])==r,'Immutable reference '+r['path'])
 snaps=load(S/'snapshots.json');require([r['path'] for r in snaps]==sorted(set(r['path'] for r in snaps)),'Snapshot order');drift=[]
 require(MUTABLE.issubset({r['path'] for r in snaps}),'All four ledgers frozen')
 for r in snaps:
  inactive(r['path']);require(row(r['snapshot'])==dict(path=r['snapshot'],sha256=r['sha256'],bytes=r['bytes']),'Snapshot immutable bytes')
  if r['path'] in MUTABLE:
   if sha(read(r['path']))!=r['sha256']:drift.append(r['path'])
  else:require(row(r['path'])==dict(path=r['path'],sha256=r['sha256'],bytes=r['bytes']),'Original immutable reference '+r['path'])
 require(load(S/'snapshots/sources/upstream.json')['commit']==PIN,'Upstream identity')
 manifest=load(S/'read-manifest.json')
 for r in manifest:
  inactive(r['path']);b=read(r['path']);require(sha(b)==r['sha256'] and b.count(b'\n')==r['raw_lf'] and b.endswith(b'\n')==r['terminal_lf'],'Read bytes/conventions')
  t=json.loads(b)[r['field']] if r['field'] is not None else b.decode();ls=t.splitlines();a,z=r['start'],r['end']
  require(len(ls)==r['total'] and 1<=a<=z<=len(ls),'Read range');require(sha('\n'.join(ls[a-1:z]).encode())==r['range_sha256'],'Exact read range hash')
 def covered(path,field,total):
  union={i for r in manifest if r['path']==str(path) and r['field']==field for i in range(r['start'],r['end']+1)}
  return set(range(1,total+1)).issubset(union)
 for n,(slug,digest) in TASKS.items():
  stem=f'iteration{n}-{slug}-task';p=S/'snapshots/frontier/iterations'/(stem+'.json');require(sha(read(p))==digest,'Mandatory task hash')
  d=load(p);brief=S/'decoded'/(stem+'-brief.txt');other=S/'decoded'/(stem+'-other.json')
  require(read(brief).decode()==d['brief']+'\n','Exact decoded brief');require(load(other)=={k:v for k,v in d.items() if k!='brief'},'Every other decoded field')
  require(covered(brief,None,len(d['brief'].splitlines())) or covered(p,'brief',len(d['brief'].splitlines())),'Complete recursive brief coverage')
  require(covered(other,None,len(read(other).decode().splitlines())),'All nonbrief fields supplied')
 current=load(S/'snapshots/frontier/iterations/iteration135-complex-analysis-discovery-task.json')['brief']
 report=current.split('--- FULL I132 REPORT ---\n',1)[1].split('\n--- FINAL PARENT I132 RESPONSE ---',1)[0]
 require(report.strip()==read(S/'snapshots/frontier/iterations/i132-discrete-probability-discovery.md').decode().strip(),'Full original report in supplied task')
 parent=json.loads(current.split('--- FINAL PARENT I132 RESPONSE ---\n',1)[1]);require(parent==load(S/'snapshots/frontier/experiments/i132-parent-verification.json'),'Full finalized parent receipt')
 require(parent['accepted_count']==8 and parent['remaining_count']==2,'Inherited count')
 for r in load(S/'ledger-excerpts.json'):
  b=read(r['path']);require(sha(b)==r['sha256'] and b.decode().splitlines()[r['line']-1]==r['text'],'Retained ledger excerpt')
 domain=load('frontier/sources/i114_quantum_information_discovery/search-domain.json');roots=load(S/'family-roots.json')
 require(roots==sorted(set(roots)) and len(roots)==9,'Family roots');require(load(S/'selected-inventory.json')==[r for r in domain if r['path'].split('/')[1] in roots],'Complete selected representations')
 lexical={}
 for label in ('source','overlap'):
  q=load(S/(label+'-query.json'));require(q['files']==sorted(set(q['files'])) and q['flags']=='IGNORECASE','Lexical domain');out=[];pat=re.compile(q['pattern'],re.I)
  for p in q['files']:
   inactive(p)
   for n,l in enumerate(read(p).decode().splitlines(),1):
    for mt in pat.finditer(l):out.append(dict(path=p,line=n,start=mt.start(),end=mt.end(),text=mt.group(),line_text=l))
  require(out==load(S/(label+'-results.json')),'Exact lexical occurrence multiset '+label);lexical[label]=len(out)
 http=load(S/'http-log.json');bindings=load(S/'html-bindings.json')
 convert=runpy.run_path('frontier/experiments/i114_quantum_information_discovery/html_text.py')['convert']
 require(len(http)==len(bindings)==6,'Selected external versions')
 for r,v in zip(http,bindings):
  require(r['status']==200 and row(r['path'])==dict(path=r['path'],sha256=r['sha256'],bytes=r['bytes']),'HTTP bytes')
  require(r['url']==v['url'] and row(v['html']['path'])==v['html'] and row(v['text']['path'])==v['text'],'HTML bindings')
  require(convert(read(v['html']['path']).decode()).encode()==read(v['text']['path']),'Deterministic HTML view')
 require(load(S/'failure-log.json')['scope']=='Acquisition/display limitations; not universal proof evidence','Failure log scope')
 # Only immutable prefixes execute. No inherited diagnostics or recursive replay.
 recent=immutable_prefix('frontier/experiments/i132_discrete_probability_discovery/verify.py','df5206d9bdb329e96f8e0972603ca738f19275ac28bd8f7dc202dd0a841606ed','saved','return dict(files=len(files), reads=len(manifest), lexical=lexical, i129=prefix)')
 flat=immutable_prefix('frontier/experiments/i123_thermal_production_stability/verify.py','feef6639e9a4c9916f4b845f771263e795a25fbee83227c0716e339d7a5ef4c3','diagnostics',"return dict(original_positions=len(domain), original_bytes=original_bytes, domain_kinds=kinds, corpus_traversals=1, tree_entries=len(tree['tree']), manuscript_roots=len(roots))")
 require(flat['original_positions']==10373 and flat['tree_entries']==13223 and flat['manuscript_roots']==749 and flat['domain_kinds']['outside_pdf']==776,'One complete flat replay')
 # ALL immutable bytes and bindings above precede the sole new diagnostic call.
 diagnostic=runpy.run_path(str(X/'check.py'))['run']();require(diagnostic['status']=='PASS','New finite diagnostics')
 inherited=parent['result'];historical={k:inherited[k] for k in ('inherited_diagnostics','i126_diagnostics','i129_diagnostics','i132_diagnostics')}
 if not pre:require(receipt['new_diagnostics']==diagnostic,'Diagnostic identity since preseal')
 print(json.dumps(dict(status='PASS',mode='preseal-read-only' if pre else 'sealed-read-only',globally_sorted_exact_inventory=True,all_immutable_checks_before_diagnostics=True,**flat,recent_immutable_prefix=recent,inherited_diagnostics_mode='Frozen parent receipt only; no inherited diagnostics rerun',inherited_diagnostic_receipts=historical,new_diagnostics=diagnostic,read_records=len(manifest),lexical_occurrences=lexical,html_views=len(bindings),owned_files_without_seal=len(files),owned_directories=len(dirs),permitted_mutable_drift=sorted(drift),validated_files=validated,scope='Immutable evidence and finite rational identities only; no universal analytic proof, endpoint result, substantiality or priority certification'),indent=2))
if __name__=='__main__':main()
