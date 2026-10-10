"""Offline read-only I130 replay, expanded flat from I127; no inherited verifier is executed. All immutable material BEFORE diagnostics.
No recursive verifier, network, writes, bytecode, repair, or resealing.
--preseal is allowed only before the unique final seal exists.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,re,runpy,os
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i124_fractal_incidence_discovery';E=ROOT/'frontier/experiments/i124_fractal_incidence_discovery'
V=ROOT/'frontier/sources/i127_diagonal_pinned_distance';EE=ROOT/'frontier/experiments/i127_diagonal_pinned_distance'
OLD=[ROOT/'frontier/sources'/n for n in ['i112_inverse_boundary_discovery','i115_physical_elasticity_continuation','i118_physical_quotient_angular','i121_physical_transfer_bound','i124_fractal_incidence_discovery']]
OLDHASH=['6b0e58e12bbc8af8e4ed3f66c7cb6d38963da6fce6370c4f3e840b91cae1a42e','e038e926e30d7505ecb9cd398f785a525d529799dd79a3803c472cc3ab800432','1256b9c7c8371486805557acddadfc2d851cb26268297155c989b1ff56d4169d','4cf2dca95899c5d68c02f87161e83230665b2c2532301848934f5dde52193278','0c47be17de45a72348387eccd304cc62a529e3c692ef5c5b26f979166f3e665f']
LEDGERS=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
W=ROOT/'frontier/sources/i130_spectral_harmonic_discovery';WE=ROOT/'frontier/experiments/i130_spectral_harmonic_discovery'
def audit(event,args):
 if event=='open':
  mode,flags=args[1:3]
  assert not (isinstance(mode,str) and any(c in mode for c in 'wax+')),('write forbidden',args[0])
  assert not (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),('write flags forbidden',args[0])
 if event.startswith('socket.') or event in {'os.mkdir','os.remove','os.rename','os.rmdir','os.link','os.symlink','os.chmod','os.truncate','os.utime','os.system','os.exec','os.posix_spawn','os.fork'}:raise AssertionError(('mutation/network forbidden',event))
 if event=='subprocess.Popen':
  raise AssertionError(('subprocess forbidden',args[1]))
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
 own_pre=sys.argv[1:]==['--preseal'];assert not sys.argv[1:] or own_pre
 wi=data(W/'inventory.json');wp=wi['owned_paths'];assert wp==sorted(set(wp))
 wa=files([W,WE])|{'frontier/iterations/i130-spectral-harmonic-discovery.md'}
 ws=wi['seal_path'];wv=rel(WE/'validation.json');wanted=set(wp)
 assert wi['allowed_live_ledger_drift']==LEDGERS and wi['selective_pdf_replay_limit']==0
 if own_pre:
  assert not (ROOT/ws).exists(),'preseal forbidden after final seal'
  if wv not in wa:wanted.remove(wv)
  assert wa==wanted,dict(extra=sorted(wa-wanted),missing=sorted(wanted-wa))
 else:
  assert wa==wanted|{ws},dict(extra=sorted(wa-wanted-{ws}),missing=sorted(wanted-wa))
  wseal=data(ROOT/ws);assert list(wseal['sha256'])==wp
  for p,h in wseal['sha256'].items():assert sha(read(p))==h,('I130 immutable',p)
  wval=data(WE/'validation.json');assert wval['status']=='PASS' and wval['exit_code']==0
 wrefs=data(W/'immutable-references.json')
 assert [r['path'] for r in wrefs]==sorted({r['path'] for r in wrefs})
 for r in wrefs:assert sha(read(r['path']))==r['sha256'],('I130 direct immutable',r['path'])
 assert sha((V/'seal.json').read_bytes())=='d917b10cbe80dfc969c6a3dce949ab6ee5968baa91ef76da01e6f9b3bb4c3cad'
 # I127 itself is an inherited immutable bundle, always sealed, never executed.
 pre=False
 inv=data(V/'inventory.json');expected=set(inv['owned_paths']);sealpath=inv['seal_path'];validation=rel(EE/'validation.json')
 assert inv['allowed_live_ledger_drift']==LEDGERS and inv['selective_pdf_replay_limit']==0
 actual=files([V,EE])|{'frontier/iterations/i127-diagonal-pinned-distance.md'}
 if pre:
  assert not (ROOT/sealpath).exists(),'preseal forbidden after final seal'
  if validation not in actual:expected.remove(validation)
  assert actual==expected,dict(extra=sorted(actual-expected),missing=sorted(expected-actual))
 else:
  assert actual==expected|{sealpath},dict(extra=sorted(actual-expected-{sealpath}),missing=sorted(expected-actual))
  sealed=data(ROOT/sealpath);assert set(sealed['sha256'])==expected
  for p,h in sealed['sha256'].items():assert sha(read(p))==h,('owned immutable',p)
  val=data(EE/'validation.json');assert val['status']=='PASS' and val['exit_code']==0
 refs=data(V/'immutable-references.json')
 for x in refs:assert sha(read(x['path']))==x['sha256'],('immutable direct',x['path'])
 inherited_count=0
 for old,h in zip(OLD,OLDHASH):
  assert sha((old/'seal.json').read_bytes())==h,('inherited seal',rel(old))
  oi=data(old/'inventory.json');os_=data(old/'seal.json');assert set(os_['sha256'])==set(oi['owned_paths'])
  oe=ROOT/rel(old).replace('/sources/','/experiments/')
  reports={p for p in oi['owned_paths'] if p.startswith('frontier/iterations/')}
  assert files([old,oe])|reports==set(oi['owned_paths'])|{oi['seal_path']},('inherited exact inventory',rel(old))
  for p,hh in os_['sha256'].items():assert sha(read(p))==hh,('inherited sealed',p)
  for x in data(old/'immutable-references.json'):assert sha(read(x['path']))==x['sha256'],('inherited immutable',x['path'])
  inherited_count+=len(os_['sha256'])
 f124=data(S/'input-freeze.json');task124=read(f124['task']).decode()
 assert data(ROOT/f124['task_snapshot'])['brief']==task124
 check_parts(task124,f124['markers'],f124['parts'],S)
 recursive=read(f124['recursive_task_snapshot'])
 assert sha(recursive)==f124['recursive_task_sha256']=='b4495a8eee4deb1c6578820947eb2d0a1ca725813f1b380cbcf98c0712620a96'
 assert json.loads(recursive)['brief']==(OLD[3]/'supplied-task.txt').read_text()
 report=read('frontier/iterations/i121-physical-transfer-bound.md')
 assert sha(report)==f124['original_report_sha256']=='fe041ed219377b9aa5b13529511d655aa526f0e849c998b9ff30356dbd1f624d'
 assert (S/'supplied-original-i121-report.txt').read_text().strip()==report.decode().strip()
 assert (S/'snapshots/frontier/iterations/i121-physical-transfer-bound.md').read_bytes()==report
 p121=data(S/'snapshots/frontier/experiments/i121-parent-verification.json')
 assert p121==data(S/'supplied-finalized-i121-parent-response.txt')==data(ROOT/'frontier/experiments/i121-parent-verification.json')
 assert p121['seal_sha256']==OLDHASH[3];check_parent(p121)
 assert (S/'original-i118-task.json').read_bytes()==(OLD[3]/'original-i118-task.json').read_bytes()
 assert (S/'original-i118-brief.txt').read_bytes()==(OLD[3]/'original-i118-brief.txt').read_bytes()
 # Every original, supplied record, immutable snapshot and finalized parent is checked flat.
 fr=data(OLD[3]/'input-freeze.json');task=read(fr['task']).decode();assert data(OLD[3]/'i121-task-snapshot.json')['brief']==task
 check_parts(task,fr['markers'],fr['parts'],OLD[3])
 original=(OLD[3]/'original-i118-task.json').read_bytes();assert sha(original)==fr['original_i118_task_sha256']=='19806b3abe8937dbeb11fc72a8cb47a0c52d7bf2e7cee0a0880eefc2b5b2dbf1'
 assert original==(OLD[2]/'task-launch-snapshot.json').read_bytes()
 assert json.loads(original)['brief'].encode()==(OLD[3]/'original-i118-brief.txt').read_bytes()==(OLD[2]/'supplied-task.txt').read_bytes()
 assert (OLD[3]/'original-i118-report.md').read_bytes()==read('frontier/iterations/i118-physical-quotient-angular.md')
 assert (OLD[3]/'supplied-original-i118-report.txt').read_text().strip()==(OLD[3]/'original-i118-report.md').read_text().strip()
 assert (OLD[3]/'finalized-i118-parent-response.json').read_bytes()==read('frontier/experiments/i118-parent-verification.json')
 parent=data(OLD[3]/'finalized-i118-parent-response.json');assert data(OLD[3]/'supplied-finalized-i118-parent-response.txt')==parent and parent['seal_sha256']==OLDHASH[2];check_parent(parent)
 f=data(OLD[2]/'input-freeze.json');t=read(f['task']).decode();check_parts(t,f['markers'],f['parts'],OLD[2])
 assert data(OLD[2]/'task-launch-snapshot.json')['brief']==t
 assert (OLD[2]/'original-i115-report.md').read_bytes()==read(f['original_report'])
 assert (OLD[2]/'finalized-i115-parent-response.json').read_bytes()==read(f['parent'])
 p115=data(OLD[2]/'finalized-i115-parent-response.json');assert data(OLD[2]/'supplied-finalized-parent-response.txt')==p115 and p115['seal_sha256']==OLDHASH[1];check_parent(p115)
 f=data(OLD[1]/'input-freeze.json');t=read(f['full_task']).decode();check_parts(t,f['markers'],f['parts'],OLD[1])
 assert read(f['on_disk_report'])==read('frontier/iterations/i112-inverse-boundary-discovery.md')
 p112=data(OLD[1]/'parent-response.txt');assert p112['seal_sha256']==OLDHASH[0];check_parent(p112)
 check_parent(data(ROOT/'frontier/experiments/i112-parent-verification.json'))
 # Complete original Git/SHA/text mapping and all historical/new lexical searches, one pass.
 domain=data(OLD[0]/'search-domain.json');assert domain==data(ROOT/'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json')
 tree=data(OLD[0]/'snapshots/sources/preprints-tree.json')['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
 assert len(tree)==13223 and len(blobs)==10373 and sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)==749
 assert len(domain)==10373 and len({x['path'] for x in domain})==10373 and {x['path'] for x in domain}==set(blobs)
 lexical=[data(old/'lexical-search.json') for old in OLD]+[data(V/'lexical-search.json'),data(W/'lexical-search.json')];patterns={}
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
 for tp in [OLD[1]/'title-screen.json',S/'title-screen.json']:
  ts=data(tp);assert ts['titles']==sorted({x['path'].split('/')[1] for x in domain if re.search(ts['expression'],x['path'].split('/')[1])})
 bypath={x['path']:x for x in domain}
 for x in data(S/'selected-source-bindings.json'):
  assert x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path']
  assert {k:v for k,v in x.items() if k!='url'}==bypath[x['path']]
 overlap=data(S/'overlap-search.json');rx=re.compile(overlap['expression']);oh=[]
 for p in overlap['paths']:
  for i,l in enumerate(read(p).decode().splitlines(),1):
   mm=list(rx.finditer(l))
   if mm:oh.append(dict(path=p,splitlines_line=i,text=l,spans=[list(m.span()) for m in mm]))
 assert oh==overlap['results']
 passages=0
 for manifest in [old/'read-manifest.json' for old in OLD]+[V/'read-manifest.json',W/'read-manifest.json']:
  for p in data(manifest)['passages']:
   b=read(p['local']);assert sha(b)==p['file_sha256'],('passage file',p['local'])
   assert p['convention'] in {'splitlines','LF','lf','splitlines()','split("\\n")','LF split; form feeds preserved'} or 'LF' in p['convention'],p['convention']
   ls=b.decode().splitlines() if p['convention']=='splitlines' else b.decode().split('\n')
   assert 1<=p['start']<=p['end']<=len(ls)
   part='\n'.join(ls[p['start']-1:p['end']]);assert sha(part.encode())==p['passage_sha256']
   if 'passage' in p:assert part==p['passage']
   if 'line_count' in p:assert p['line_count']==len(ls)
   passages+=1
 for old in [S,V,W]:
  for x in data(old/'retrieval.json'):
   if 'error' not in x:assert sha(read(x['path']))==x['sha256']
 assert data(S/'literature/upstream-head.json')['object']['sha']==PIN
 for n,v in [('liu',3),('bop',1),('iy',1),('ilx',2),('repair',1)]:
  versions=[int(x) for x in re.findall(r'<strong>\[v(\d+)\]</strong>',(S/'literature'/(n+'-current.html')).read_text())]
  assert versions and max(versions)==v,('current primary version',n,versions)
 # I127 original exact recursive record; every decoded field, not just a brief hash.
 f127=data(V/'input-freeze.json');t127=data(ROOT/f127['task127']);brief=read(f127['brief127']).decode()
 assert t127['brief']==brief
 check_parts(brief,f127['markers'],f127['parts'],V)
 for x in f127['recursive_tasks']:assert sha(read(x['path']))==x['sha256']
 task124=data(V/'snapshots/frontier/iterations/iteration124-fractal-incidence-discovery-task.json')
 assert task124==data(V/'original-i124-decoded.json') and task124['brief']==(V/'original-i124-brief.txt').read_text()
 assert sha((V/'snapshots/frontier/iterations/iteration124-fractal-incidence-discovery-task.json').read_bytes())=='bd1ed58fb0adf6d63d0b36b67a5092f78f1d2063cf19317dfadad70ee8c6f240'
 assert (V/'original-i121-task.json').read_bytes()==(S/'snapshots/frontier/iterations/iteration121-physical-transfer-bound-task.json').read_bytes()
 assert data(V/'original-i121-task.json')['brief']==(V/'original-i121-brief.txt').read_text()
 assert (V/'original-i118-task.json').read_bytes()==(S/'original-i118-task.json').read_bytes()
 assert data(V/'original-i118-task.json')['brief']==(V/'original-i118-brief.txt').read_text()
 assert (V/'supplied-original-i124-report.txt').read_text().strip()==read('frontier/iterations/i124-fractal-incidence-discovery.md').decode().strip()
 parent124=data(ROOT/f127['frozen_parent'])
 assert parent124==data(V/'supplied-finalized-i124-parent-response.txt')==data(ROOT/'frontier/experiments/i124-parent-verification.json')
 assert parent124['seal_sha256']==OLDHASH[-1]
 for x in parent124['parent_review']['source_reads']:
  bb=read(x['path']);assert sha(bb)==x['sha256'];ll=bb.decode().splitlines()
  for r in x['ranges']:assert sha('\n'.join(ll[r['start']-1:r['end']]).encode())==r['sha256']
 # Pure read-only HTML representation check, after all immutable bytes have been checked.
 extract=runpy.run_path(str(ROOT/'frontier/experiments/i124_fractal_incidence_discovery/extract_html.py'))['extract']
 for x in data(V/'html-bindings.json')+data(W/'html-bindings.json'):
  h=read(x['html']);tt=read(x['text'])
  assert sha(h)==x['html_sha256'] and sha(tt)==x['text_sha256']
  assert extract(h.decode()).encode()==tt
 for n,v in [('glw',1),('liu',3),('iy',1),('repair',1)]:
  versions=[int(x) for x in re.findall(r'<strong>\[v(\d+)\]</strong>',(V/'literature'/(n+'-current.html')).read_text())]
  assert versions and max(versions)==v,('fresh version',n,versions)
 # Full I130 decoded input, exact originals and all recursively required fields.
 fr=data(W/'input-freeze.json');t=data(ROOT/fr['task130']);t127=data(ROOT/fr['task127'])
 assert sha(read(fr['task127']))=='49dafeac25ffa649bdf42ad11bbcac47f508aa1dd023958cbf3e78d7a7953f77'
 assert t['brief']==(W/'i130-decoded-brief.txt').read_text()
 assert t127['brief']==(W/'i127-decoded-brief.txt').read_text()
 assert {k:v for k,v in t.items() if k!='brief'}==data(W/'i130-other-fields.json')
 assert {k:v for k,v in t127.items() if k!='brief'}==data(W/'i127-other-fields.json')
 check_parts(t['brief'],fr['markers'],fr['parts'],W)
 assert (W/'supplied-original-i127-report.txt').read_text().strip()==read('frontier/iterations/i127-diagonal-pinned-distance.md').decode().strip()
 par=data(W/'supplied-finalized-i127-parent-response.txt')
 assert par==data(W/'snapshots/frontier/experiments/i127-parent-verification.json')==data(ROOT/'frontier/experiments/i127-parent-verification.json')
 assert par['seal_sha256']=='d917b10cbe80dfc969c6a3dce949ab6ee5968baa91ef76da01e6f9b3bb4c3cad'
 for z in par['parent_review']['complete_files']:assert sha(read(z['path']))==z['sha256']
 for z in par['parent_review']['source_reads']:
  bb=read(z['path']);assert sha(bb)==z['sha256'];ll=bb.decode().splitlines()
  for r in z['ranges']:assert sha('\n'.join(ll[r['start']-1:r['end']]).encode())==r['sha256']
 for z in data(W/'recursive-freeze.json')['records']:
  bb=read(z['path']);assert sha(bb)==z['sha256'];assert list(json.loads(bb))==z['all_fields']
 for z in data(W/'selected-domain.json'):assert z==bypath[z['path']]
 wo=data(W/'overlap-search.json');rx=re.compile(wo['expression']);wr=[]
 for p in wo['paths']:
  for i,l in enumerate(read(p).decode().splitlines(),1):
   mm=list(rx.finditer(l))
   if mm:wr.append(dict(path=p,splitlines_line=i,text=l,spans=[list(m.span()) for m in mm]))
 assert wr==wo['results']
 versions_seen={}
 for n,v in [('huang',1),('lwx',1),('cai-lai',2),('logunov',2),('xu',1),('brustad',1)]:
  versions=[int(z) for z in re.findall(r'<strong>\[v(\d+)\]</strong>',(W/'literature'/(n+'-current.html')).read_text())]
  assert versions and max(versions)==v,('I130 primary version',n,versions)
  versions_seen[n]=v
 print('Entire immutable/corpus/lexical/passage preflight: PASS; diagnostics begin now',file=sys.stderr,flush=True)
 # Only I130 finite instances; no inherited verifier or diagnostic invoked.
 own=runpy.run_path(str(WE/'diagnostics.py'))['check']();assert own==data(WE/'diagnostic-result.json')
 drift=[p for p in LEDGERS if sha(read(p))!=sha((W/'snapshots'/p).read_bytes())]
 print(json.dumps(dict(status='PASS',mode='preseal' if own_pre else 'sealed read-only',owned_files=len(wa),inherited_sealed_artifacts=inherited_count+len(expected),immutable_direct_references=len(wrefs),tree_entries=len(tree),manuscripts=749,original_blob_positions=len(domain),inherited_pdf_text_bindings=pdfs,read_passages=passages,lexical_matched_lines={k:len(v) for k,v in computed.items()},overlap_matched_lines=len(wr),selected_pdf_reextractions=0,primary_versions=versions_seen,immutable_preflight_before_diagnostics=True,recursive_verifiers_invoked=0,inherited_diagnostic_runs='none; checked only as immutable records',new_finite_diagnostics=own['status'],allowed_live_ledger_drift_observed=drift,scope='Evidence reproduction and finite instances only; no universal analysis, fixed-metric infinite-degree theorem, substantiality, human-review or priority certification'),indent=2))
if __name__=='__main__':main()
