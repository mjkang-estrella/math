"""Offline read-only replay. Immutable validation precedes finite diagnostics.
I129 and I126 immutable prefixes, then exactly one inherited I123 flat replay.
No acquisition, extraction, writes, bytecode, subprocess, repair, or reseal.
"""
import sys
sys.dont_write_bytecode=True
import os

def readonly(event,args):
 if event=='open':
  mode=args[1];flags=args[2] if len(args)>2 else 0
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
   raise RuntimeError('Read-only replay blocked write '+repr(args[0]))
 if event.startswith(('socket.','subprocess.')) or event in {'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.utime','os.truncate','os.link','os.symlink','shutil.copyfile','os.putenv','os.unsetenv','os.exec','os.posix_spawn'}:
  raise RuntimeError('Offline read-only replay blocked '+event)
sys.addaudithook(readonly)
import ast,contextlib,hashlib,io,json,re,runpy
from html.parser import HTMLParser
from pathlib import Path
ROOT=Path.cwd().resolve()
S=Path('frontier/sources/i132_discrete_probability_discovery')
X=Path('frontier/experiments/i132_discrete_probability_discovery')
R=Path('frontier/iterations/i132-discrete-probability-discovery.md')
V129=Path('frontier/experiments/i129_disordered_fk_occupation/verify.py')
SHA129='bb6571ca504ed4dba42216072b6313f01d20e232acc62fd5e91132e6605a7c0f'
V123=Path('frontier/experiments/i123_thermal_production_stability/verify.py')
SHA123='feef6639e9a4c9916f4b845f771263e795a25fbee83227c0716e339d7a5ef4c3'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}

def require(ok,msg):
 if not ok:raise AssertionError(msg)
def read(p):
 p=Path(p);require(p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(ROOT),'Missing/symlink/outside '+str(p));return p.read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(read(p))
def row(p):
 b=read(p);return dict(path=str(p),sha256=sha(b),bytes=len(b))
def inactive(p):require(not re.search(r'(?:^|/)(?:i|iteration)(?:130|131)(?:[-_/])',p),'Active output dependency '+p)
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

class View(HTMLParser):
 def __init__(self):super().__init__(convert_charrefs=True);self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip and d.strip():self.parts.append(d.strip())

def validate_i129_prefix():
 source=read(V129);require(sha(source)==SHA129,'Exact original I129 verifier')
 tree=ast.parse(source,filename=str(V129));mains=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main'];require(len(mains)==1,'I129 main structure');main=mains[0]
 cuts=[i for i,n in enumerate(main.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='saved' for t in n.targets)]
 require(len(cuts)==1,'Unique immutable-prefix boundary')
 prefix=main.body[:cuts[0]]
 require(any(isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='inherited126' for t in n.targets) for n in prefix),'Includes I126 immutable prefix')
 main.body=prefix+ast.parse('return dict(files=len(files), reads=len(manifest), lexical=len(results), drift=sorted(drift), i126=inherited126)').body
 require(isinstance(tree.body[-1],ast.If),'Original entrypoint');tree.body.pop();ast.fix_missing_locations(tree)
 ns={'__name__':'i129_immutable_prefix','__file__':str(V129)}
 exec(compile(tree,str(V129)+' [immutable prefix only]','exec'),ns)
 saved=sys.argv;sys.argv=[str(V129)]
 try:return ns['main']()
 finally:sys.argv=saved

def main():
 require(sys.argv[1:] in ([],['--preseal']),'Only --preseal supported')
 preseal=bool(sys.argv[1:]);files,dirs=inventory()
 require(files==sorted(set(files)) and dirs==sorted(set(dirs)),'Globally sorted exact inventory')
 validated=[row(p) for p in files if p!=str(S/'preseal-validation.json')]
 if preseal:require(not (S/'seal.json').exists(),'Preseal refuses existing seal')
 else:
  seal=load(S/'seal.json');require(seal['schema']=='i132-one-final-seal-v1' and seal['globally_sorted_exact_inventory'] is True,'Seal schema and explicit assertion')
  require(seal['files']==[row(p) for p in files] and seal['directories']==dirs,'All owned immutable bytes and exact globally sorted inventory')
  receipt=load(S/'preseal-validation.json');require(receipt['status']=='PASS' and receipt['validated_files']==validated,'Preseal exact final bytes')
 deps=load(S/'engine-dependencies.json')
 require([r['path'] for r in deps]==sorted(set(r['path'] for r in deps)),'Execution dependency order')
 for r in deps:inactive(r['path']);require(row(r['path'])==r,'Immutable execution dependency '+r['path'])
 require(sha(read(V123))==SHA123,'Flat engine identity')
 refs=load(S/'references.json');drift=[]
 require({r['path'] for r in refs if r['mutable']}==MUTABLE,'Only four mutable ledgers')
 require(len(refs)==len({r['path'] for r in refs}),'Duplicate references')
 for r in refs:
  inactive(r['path']);require(row(r['snapshot'])==dict(path=r['snapshot'],sha256=r['sha256'],bytes=r['bytes']),'Immutable snapshot')
  if r['mutable']:
   if sha(read(r['path']))!=r['sha256']:drift.append(r['path'])
  else:require(row(r['path'])==dict(path=r['path'],sha256=r['sha256'],bytes=r['bytes']),'Original immutable reference '+r['path'])
 additional=load(S/'additional-references.json')
 require([r['path'] for r in additional]==sorted(set(r['path'] for r in additional)),'Additional reference order')
 for r in additional:
  inactive(r['path']);require(r['path'] not in MUTABLE,'Mutable path in immutable references');require(row(r['path'])==r,'Additional immutable reference')
 domain=load('frontier/sources/i114_quantum_information_discovery/search-domain.json');require(len(domain)==10373,'Original position count');by={r['path']:r for r in domain}
 manifest=load(S/'read-manifest.json')
 for r in manifest:
  inactive(r['local']);b=read(r['local']);raw=b.decode('utf-8')
  require((sha(b),len(b),b.count(b'\n'),len(raw.splitlines()),b.endswith(b'\n'))==(r['sha256'],r['bytes'],r['lf_count'],r['splitlines_count'],r['ends_lf']),'Read bytes and conventions')
  t=json.loads(raw)[r['field']] if r['field'] is not None else raw
  if not isinstance(t,str):t=json.dumps(t,indent=2,ensure_ascii=False)
  ls=t.splitlines();a,z=r['start'],r['end'];require(len(ls)==r['decoded_lines'] and 1<=a<=z<=len(ls),'Decoded range');require(sha('\n'.join(ls[a-1:z]).encode())==r['range_sha256'],'Read range hash')
  if 'domain_path' in r:require(by[r['domain_path']]['local']==r['local'] and r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['domain_path'],'Pinned source mapping')
 tasks={'129-disordered-fk-occupation':'96547471b969b143cc84a80c6efdc12897315973c2ab322c4ae5ee18cbdd9147','126-random-geometry-discovery':'38e2d007ce9cb236a9601392a586e72263279bdc28744e394d8997cd457f6651','123-thermal-production-stability':'c0a4216b88cf7bde8e7ff4517c0d4fb2144e5457d1ab57fc5315f1d739653172','120-thermal-trace-stability':'d1b09ad8939c4842ddba3c672336e31f52ea6b0ec0433ac6e0ace2cbacad292d'}
 for suffix,digest in tasks.items():
  p='frontier/iterations/iteration'+suffix+'-task.json';require(sha(read(p))==digest,'Required original task')
  for k,v in load(p).items():
   t=v if isinstance(v,str) else json.dumps(v,indent=2,ensure_ascii=False)
   covered={i for r in manifest if r['local'] in (p,str(S/'snapshots'/p)) and r['field']==k for i in range(r['start'],r['end']+1)}
   require(covered==set(range(1,len(t.splitlines())+1)),'Full decoded recursive field '+p+':'+k)
 task132=load(S/'snapshots/frontier/iterations/iteration132-discrete-probability-discovery-task.json')['brief']
 orig=task132.split('--- ORIGINAL I129 REPORT ---\n',1)[1].split('\n--- FINALIZED I129 PARENT RESPONSE ---',1)[0]
 require(orig.strip()==read(S/'snapshots/frontier/iterations/i129-disordered-fk-occupation.md').decode().strip(),'Original report exact in current supplied brief')
 parent=json.loads(task132.split('--- FINALIZED I129 PARENT RESPONSE ---\n',1)[1]);require(parent==load(S/'snapshots/frontier/experiments/i129-parent-verification.json'),'Full finalized parent response')
 roots=load(S/'family-roots.json');require(roots==sorted(set(roots)) and len(roots)==18,'Selected family roots');selected=load(S/'selected-inventory.json');require(selected==[r for r in domain if r['path'].split('/')[1] in roots],'Complete family source inventory')
 lexical={}
 for prefix in ('overlap','source'):
  query=load(S/(prefix+'-query.json'));require(query['files']==sorted(set(query['files'])) and query['flags']=='IGNORECASE','Lexical domain');result=[];pattern=re.compile(query['pattern'],re.I)
  for p in query['files']:
   inactive(p)
   for n,line in enumerate(read(p).decode().splitlines(),1):
    for m in pattern.finditer(line):result.append(dict(path=p,line=n,start=m.start(),end=m.end(),text=m.group(),line_text=line))
  require(result==load(S/(prefix+'-results.json')),'Exact lexical occurrence multiset '+prefix);lexical[prefix]=len(result)
 http=load(S/'http-log.json');views=0
 for r in http:
  if 'path' not in r:require('error' in r,'Failed retrieval recorded');continue
  require(row(r['path'])==dict(path=r['path'],sha256=r['sha256'],bytes=r['bytes']) and r['status']==200,'HTTP byte provenance')
  if 'view' in r:
   b=read(r['view']);require(sha(b)==r['view_sha256'],'HTML view hash');parser=View();parser.feed(read(r['path']).decode('utf-8'));require('\n'.join(parser.parts).encode()==b,'Deterministic HTML view');views+=1
 for r in load(S/'pdf-bindings.json'):
  require(row(r['pdf']['path'])==r['pdf'] and row(r['text']['path'])==r['text'] and r['exit_code']==0,'Fresh PDF/text immutable binding')
 failures=load(S/'failure-log.json');require(failures['scope']=='Acquisition/display limitations; not universal proof evidence','Failure-log scope')
 # All new and both recent inherited immutable packages are validated first.
 prefix=validate_i129_prefix()
 # Exactly one flat engine validates the complete older packages and corpus,
 # then (and only then) runs its immutable finite diagnostic programs.
 saved=sys.argv;sys.argv=[str(V123)];capture=io.StringIO()
 try:
  with contextlib.redirect_stdout(capture):runpy.run_path(str(V123),run_name='__main__')
 finally:sys.argv=saved
 inherited=json.loads(capture.getvalue());require(inherited['status']=='PASS' and inherited['corpus_traversals']==1 and inherited['original_positions']==10373 and inherited['domain_kinds']['outside_pdf']==776,'One complete flat corpus/PDF replay')
 diag126=runpy.run_path('frontier/experiments/i126_random_geometry_discovery/check.py')['run']()
 diag129=runpy.run_path('frontier/experiments/i129_disordered_fk_occupation/check.py')['run']()
 own=runpy.run_path(str(X/'check.py'))['run']()
 print(json.dumps(dict(status='PASS',mode='preseal-read-only' if preseal else 'sealed-read-only',globally_sorted_exact_inventory=True,all_immutable_checks_before_diagnostics=True,corpus_traversals=1,original_positions=inherited['original_positions'],original_bytes=inherited['original_bytes'],domain_kinds=inherited['domain_kinds'],i129_immutable_prefix=prefix,inherited_diagnostics=inherited['diagnostics'],i126_diagnostics=diag126,i129_diagnostics=diag129,i132_diagnostics=own,own_lexical_occurrences=lexical,own_read_records=len(manifest),own_html_views=views,owned_files_without_seal=len(files),owned_directories=len(dirs),permitted_mutable_drift=sorted(drift),validated_files=validated,scope='Immutable evidence and finite exact diagnostics; no universal-proof, all-singularity conditional theorem, asymptotic or substantiality certification'),indent=2))
if __name__=='__main__':main()
