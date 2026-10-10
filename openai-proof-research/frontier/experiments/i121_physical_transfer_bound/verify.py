"""Offline read-only I121 replay. All immutable material BEFORE diagnostics.
No recursive verifier, network, writes, bytecode, repair, or resealing.
--preseal is allowed only before the unique final seal exists.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,re,subprocess,runpy,os
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i121_physical_transfer_bound';E=ROOT/'frontier/experiments/i121_physical_transfer_bound'
OLD=[ROOT/'frontier/sources'/n for n in ['i112_inverse_boundary_discovery','i115_physical_elasticity_continuation','i118_physical_quotient_angular']]
OLDHASH=['6b0e58e12bbc8af8e4ed3f66c7cb6d38963da6fce6370c4f3e840b91cae1a42e','e038e926e30d7505ecb9cd398f785a525d529799dd79a3803c472cc3ab800432','1256b9c7c8371486805557acddadfc2d851cb26268297155c989b1ff56d4169d']
LEDGERS=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def audit(event,args):
 if event=='open':
  mode,flags=args[1:3]
  assert not (isinstance(mode,str) and any(c in mode for c in 'wax+')),('write forbidden',args[0])
  assert not (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),('write flags forbidden',args[0])
 if event.startswith('socket.') or event in {'os.mkdir','os.remove','os.rename','os.rmdir','os.link','os.symlink','os.chmod','os.truncate','os.utime','os.system','os.exec','os.posix_spawn','os.fork'}:raise AssertionError(('mutation/network forbidden',event))
 if event=='subprocess.Popen':
  argv=args[1];assert isinstance(argv,list) and argv[0]=='pdftotext' and argv[1]=='-layout' and argv[-1]=='-' and len(argv)==4,('subprocess forbidden',argv)
sys.addaudithook(audit)
def read(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def data(p):return json.loads(p.read_text())
def rel(p):return str(p.relative_to(ROOT))
def files(bases):
 out=set()
 for base in bases:
  for p in base.rglob('*'):
   assert not p.is_symlink(),('symlink',rel(p))
   if p.is_file():out.add(rel(p))
 return out

def check_parent(parent):
 if 'parent_reading' not in parent:return
 for x in parent['parent_reading']['complete_files']:assert sha(read(x['path']))==x['sha256'],('parent complete file',x['path'])
 for x in parent['parent_reading'].get('passages',[]):
  b=read(x['path']);assert sha(b)==x['source_sha256'];ls=b.decode().splitlines()
  assert 1<=x['start']<=x['end']<=len(ls)
  assert sha('\n'.join(ls[x['start']-1:x['end']]).encode())==x['passage_sha256']

def check_parts(task,markers,names,base):
 for i,n in enumerate(names):
  p=task.split(markers[i],1)[1]
  if i+1<len(names):p=p.split(markers[i+1],1)[0]
  assert p.encode()==(base/n).read_bytes(),('exact supplied substring',n)

def main():
 pre=sys.argv[1:]==['--preseal'];assert not sys.argv[1:] or pre
 inv=data(S/'inventory.json');expected=set(inv['owned_paths']);sealpath=inv['seal_path'];validation=rel(E/'validation.json')
 assert inv['allowed_live_ledger_drift']==LEDGERS and inv['selective_pdf_replay_limit']==2
 actual=files([S,E])|{'frontier/iterations/i121-physical-transfer-bound.md'}
 if pre:
  assert not (ROOT/sealpath).exists(),'preseal forbidden after final seal'
  if validation not in actual:expected.remove(validation)
  assert actual==expected,dict(extra=sorted(actual-expected),missing=sorted(expected-actual))
 else:
  assert actual==expected|{sealpath},dict(extra=sorted(actual-expected-{sealpath}),missing=sorted(expected-actual))
  sealed=data(ROOT/sealpath);assert set(sealed['sha256'])==expected
  for p,h in sealed['sha256'].items():assert sha(read(p))==h,('owned immutable',p)
  val=data(E/'validation.json');assert val['status']=='PASS' and val['exit_code']==0
 refs=data(S/'immutable-references.json')
 for x in refs:assert sha(read(x['path']))==x['sha256'],('immutable direct',x['path'])
 inherited_count=0
 for old,h in zip(OLD,OLDHASH):
  assert sha((old/'seal.json').read_bytes())==h
  oi=data(old/'inventory.json');os_=data(old/'seal.json');assert set(os_['sha256'])==set(oi['owned_paths'])
  oe=ROOT/rel(old).replace('/sources/','/experiments/')
  reports={p for p in oi['owned_paths'] if p.startswith('frontier/iterations/')}
  assert files([old,oe])|reports==set(oi['owned_paths'])|{oi['seal_path']},('inherited exact inventory',rel(old))
  for p,hh in os_['sha256'].items():assert sha(read(p))==hh,('inherited sealed',p)
  for x in data(old/'immutable-references.json'):assert sha(read(x['path']))==x['sha256'],('inherited immutable',x['path'])
  inherited_count+=len(os_['sha256'])
 # Every original, supplied record, immutable snapshot and finalized parent is checked flat.
 fr=data(S/'input-freeze.json');task=read(fr['task']).decode();assert data(S/'i121-task-snapshot.json')['brief']==task
 check_parts(task,fr['markers'],fr['parts'],S)
 original=(S/'original-i118-task.json').read_bytes();assert sha(original)==fr['original_i118_task_sha256']=='19806b3abe8937dbeb11fc72a8cb47a0c52d7bf2e7cee0a0880eefc2b5b2dbf1'
 assert original==(OLD[2]/'task-launch-snapshot.json').read_bytes()
 assert json.loads(original)['brief'].encode()==(S/'original-i118-brief.txt').read_bytes()==(OLD[2]/'supplied-task.txt').read_bytes()
 assert (S/'original-i118-report.md').read_bytes()==read('frontier/iterations/i118-physical-quotient-angular.md')
 assert (S/'supplied-original-i118-report.txt').read_text().strip()==(S/'original-i118-report.md').read_text().strip()
 assert (S/'finalized-i118-parent-response.json').read_bytes()==read('frontier/experiments/i118-parent-verification.json')
 parent=data(S/'finalized-i118-parent-response.json');assert data(S/'supplied-finalized-i118-parent-response.txt')==parent and parent['seal_sha256']==OLDHASH[2];check_parent(parent)
 f=data(OLD[2]/'input-freeze.json');t=read(f['task']).decode();check_parts(t,f['markers'],f['parts'],OLD[2])
 assert data(OLD[2]/'task-launch-snapshot.json')['brief']==t
 assert (OLD[2]/'original-i115-report.md').read_bytes()==read(f['original_report'])
 assert (OLD[2]/'finalized-i115-parent-response.json').read_bytes()==read(f['parent'])
 p115=data(OLD[2]/'finalized-i115-parent-response.json');assert data(OLD[2]/'supplied-finalized-parent-response.txt')==p115 and p115['seal_sha256']==OLDHASH[1];check_parent(p115)
 f=data(OLD[1]/'input-freeze.json');t=read(f['full_task']).decode();check_parts(t,f['markers'],f['parts'],OLD[1])
 assert read(f['on_disk_report'])==read('frontier/iterations/i112-inverse-boundary-discovery.md')
 p112=data(OLD[1]/'parent-response.txt');assert p112['seal_sha256']==OLDHASH[0];check_parent(p112)
 check_parent(data(ROOT/'frontier/experiments/i112-parent-verification.json'))
 # Full corpus mapping, original Git blobs, represented texts, and all lexical results in ONE pass.
 domain=data(OLD[0]/'search-domain.json');assert domain==data(ROOT/'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json')
 tree=data(OLD[0]/'snapshots/sources/preprints-tree.json')['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
 assert len(tree)==13223 and len(blobs)==10373 and sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)==749
 assert len(domain)==10373 and len({x['path'] for x in domain})==10373 and {x['path'] for x in domain}==set(blobs)
 lexical=[data(old/'lexical-search.json') for old in OLD]+[data(S/'lexical-search.json')];patterns={}
 for lex in lexical:
  for k,v in lex['patterns'].items():assert k not in patterns;patterns[k]=re.compile(v)
 computed={k:[] for k in patterns};pdfs=0
 for x in domain:
  b=read(x['local']);o=b if x['local']==x['original_local'] else read(x['original_local'])
  assert sha(b)==x['sha256'] and sha(o)==x['original_sha256'],('corpus SHA',x['path'])
  assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']==blobs[x['path']]['sha'],('original Git position',x['path'])
  pdfs+=x['kind']=='outside_pdf'
  for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
   for k,r in patterns.items():
    mm=list(r.finditer(line))
    if mm:computed[k].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
 assert pdfs==776
 for lex in lexical:
  for k,result in lex['results'].items():assert computed[k]==result,('lexical exact membership and multiplicity',k)
 ts=data(OLD[1]/'title-screen.json');assert ts['titles']==sorted({x['path'].split('/')[1] for x in domain if re.search(ts['expression'],x['path'].split('/')[1])})
 passages=0
 for manifest in [old/'read-manifest.json' for old in OLD]+[S/'read-manifest.json']:
  for p in data(manifest)['passages']:
   b=read(p['local']);assert sha(b)==p['file_sha256'],('passage file',p['local'])
   ls=b.decode().splitlines() if p['convention']=='splitlines' else b.decode().split('\n')
   assert 1<=p['start']<=p['end']<=len(ls)
   part='\n'.join(ls[p['start']-1:p['end']]);assert sha(part.encode())==p['passage_sha256']
   if 'passage' in p:assert part==p['passage']
   if 'line_count' in p:assert p['line_count']==len(ls)
   passages+=1
 for x in data(S/'retrieval.json'):
  if 'error' not in x:assert sha(read(x['path']))==x['sha256']
 assert data(S/'literature/upstream-head.json')['object']['sha']==PIN
 assert data(OLD[2]/'literature/upstream-head.json')['object']['sha']==PIN
 assert data(OLD[1]/'literature/head.json')['object']['sha']==PIN
 assert data(OLD[0]/'literature/upstream-head.json')['sha']==PIN
 for n in ['hardy-current.html','tan-current.html','cjlt-current.html']:
  assert re.findall(r'<strong>\[v(\d+)\]</strong>',(S/'literature'/n).read_text())==['1'],('primary version',n)
 replay=data(S/'pdf-replay.json');assert replay==data(OLD[2]/'pdf-replay.json') and len(replay)==2
 for x in replay:
  out=subprocess.run(['pdftotext','-layout',str(ROOT/x['pdf']),'-'],capture_output=True,check=True)
  assert out.stdout==read(x['text']),('selective PDF bytes',x['pdf'])
 print('Entire immutable/corpus/lexical/passage/selective-PDF preflight: PASS; diagnostics begin now',file=sys.stderr,flush=True)
 # No inherited verifier is imported or executed. Each finite diagnostic runs once.
 ds=[]
 for old,n in zip(OLD,['diagnostics.py','diagnostics.py','independent_diagnostics.py']):
  oe=ROOT/rel(old).replace('/sources/','/experiments/')
  d=runpy.run_path(str(oe/n))['check']();assert d==data(oe/'diagnostic-result.json');ds.append(d['status'])
 own=runpy.run_path(str(E/'diagnostics.py'))['check']();assert own==data(E/'diagnostic-result.json')
 drift=[p for p in LEDGERS if sha(read(p))!=sha((S/'snapshots'/p).read_bytes())]
 print(json.dumps(dict(status='PASS',mode='preseal' if pre else 'sealed read-only',owned_files=len(actual),inherited_sealed_artifacts=inherited_count,immutable_direct_references=len(refs),tree_entries=len(tree),manuscripts=749,original_blob_positions=len(domain),inherited_pdf_text_bindings=pdfs,read_passages=passages,lexical_matched_lines={k:len(v) for k,v in computed.items()},selected_pdf_reextractions=len(replay),immutable_preflight_before_diagnostics=True,recursive_verifiers_invoked=0,inherited_diagnostic_runs='I112, I115, I118 once each',new_finite_diagnostics=own['status'],allowed_live_ledger_drift_observed=drift,scope='Evidence reproduction and specified finite instances only; no universal proof, transfer estimate, P112, substantiality, human-review or priority certification'),indent=2))
if __name__=='__main__':main()
