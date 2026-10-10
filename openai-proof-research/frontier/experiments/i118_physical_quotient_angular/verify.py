"""Offline, READ-ONLY I118 replay. Run python3 -B verify.py.
No network, file writes, bytecode, repairs, resealing, or recursive verifiers.
All immutable bytes and membership are checked BEFORE any finite diagnostics.
--preseal is permitted only while the final seal does not yet exist.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,re,subprocess,runpy
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i118_physical_quotient_angular'
E=ROOT/'frontier/experiments/i118_physical_quotient_angular'
OLD=[ROOT/'frontier/sources/i112_inverse_boundary_discovery',ROOT/'frontier/sources/i115_physical_elasticity_continuation']
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
LEDGERS=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
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
 for x in parent['parent_reading']['complete_files']:assert sha(read(x['path']))==x['sha256'],('parent read',x['path'])
 for x in parent['parent_reading']['passages']:
  b=read(x['path']);assert sha(b)==x['source_sha256'];part='\n'.join(b.decode().splitlines()[x['start']-1:x['end']]);assert sha(part.encode())==x['passage_sha256']

def main():
 pre=sys.argv[1:]==['--preseal'];assert not sys.argv[1:] or pre
 inv=data(S/'inventory.json');expected=set(inv['owned_paths']);sealpath=inv['seal_path'];validation=rel(E/'validation.json')
 assert inv['allowed_live_ledger_drift']==LEDGERS and inv['selective_pdf_replay_limit']==2
 actual=files([S,E])|{'frontier/iterations/i118-physical-quotient-angular.md'}
 if pre:
  assert not (ROOT/sealpath).exists(),'preseal forbidden after final seal'
  if validation not in actual:expected.remove(validation)
  assert actual==expected,dict(extra=sorted(actual-expected),missing=sorted(expected-actual))
 else:
  assert actual==expected|{sealpath},dict(extra=sorted(actual-expected-{sealpath}),missing=sorted(expected-actual))
  sealed=data(ROOT/sealpath);assert set(sealed['sha256'])==expected
  for p,h in sealed['sha256'].items():assert sha(read(p))==h,('owned',p)
  val=data(E/'validation.json');assert val['status']=='PASS' and val['exit_code']==0
 # Every directly bound immutable artifact is checked before interpreting its diagnostics.
 refs=data(S/'immutable-references.json')
 for x in refs:assert sha(read(x['path']))==x['sha256'],('immutable direct',x['path'])
 prior_seals=['6b0e58e12bbc8af8e4ed3f66c7cb6d38963da6fce6370c4f3e840b91cae1a42e','e038e926e30d7505ecb9cd398f785a525d529799dd79a3803c472cc3ab800432']
 inherited_count=0
 for old,h in zip(OLD,prior_seals):
  assert sha((old/'seal.json').read_bytes())==h
  oi=data(old/'inventory.json');os=data(old/'seal.json');assert set(os['sha256'])==set(oi['owned_paths'])
  oldexp=ROOT/rel(old).replace('/sources/','/experiments/')
  reports={p for p in oi['owned_paths'] if p.startswith('frontier/iterations/')}
  assert files([old,oldexp])|reports==set(oi['owned_paths'])|{oi['seal_path']},('inherited exact inventory',rel(old))
  for p,hh in os['sha256'].items():assert sha(read(p))==hh,('inherited sealed',p)
  for x in data(old/'immutable-references.json'):assert sha(read(x['path']))==x['sha256'],('inherited immutable',x['path'])
  inherited_count+=len(os['sha256'])
 # Preserve both supplied and on-disk originals exactly; whitespace is not normalized in stored pieces.
 fr=data(S/'input-freeze.json');task=read(fr['task']).decode()
 assert data(S/'task-launch-snapshot.json')['brief']==task
 for i,n in enumerate(fr['parts']):
  t=task.split(fr['markers'][i],1)[1]
  if i+1<len(fr['markers']):t=t.split(fr['markers'][i+1],1)[0]
  assert t.encode()==(S/n).read_bytes(),('input substring',n)
 assert (S/'original-i115-report.md').read_bytes()==read(fr['original_report'])
 assert (S/'finalized-i115-parent-response.json').read_bytes()==read(fr['parent'])
 parent=data(S/'finalized-i115-parent-response.json');assert json.loads((S/'supplied-finalized-parent-response.txt').read_text())==parent
 assert parent['seal_sha256']==prior_seals[1];check_parent(parent)
 ff=data(OLD[1]/'input-freeze.json');tt=read(ff['full_task']).decode()
 for i,n in enumerate(ff['parts']):
  t=tt.split(ff['markers'][i],1)[1]
  if i+1<len(ff['markers']):t=t.split(ff['markers'][i+1],1)[0]
  assert t.encode()==(OLD[1]/n).read_bytes()
 assert read(ff['on_disk_report'])==read('frontier/iterations/i112-inverse-boundary-discovery.md')
 parent112=data(OLD[1]/'parent-response.txt');assert parent112['seal_sha256']==prior_seals[0];check_parent(parent112)
 check_parent(data(ROOT/'frontier/experiments/i112-parent-verification.json'))
 # One full original/text pass. Mapping equality binds the inherited I88 augmentation, not just counts.
 domain=data(OLD[0]/'search-domain.json');assert domain==data(ROOT/'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json')
 tree=data(OLD[0]/'snapshots/sources/preprints-tree.json')['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
 assert len(tree)==13223 and len(blobs)==10373 and sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)==749
 assert len(domain)==10373 and len({x['path'] for x in domain})==10373 and {x['path'] for x in domain}==set(blobs)
 lexical=[data(old/'lexical-search.json') for old in OLD]+[data(S/'lexical-search.json')]
 patterns={}
 for lex in lexical:
  for k,v in lex['patterns'].items():assert k not in patterns;patterns[k]=re.compile(v)
 computed={k:[] for k in patterns};pdfs=0
 for x in domain:
  b=read(x['local']);o=b if x['local']==x['original_local'] else read(x['original_local'])
  assert sha(b)==x['sha256'] and sha(o)==x['original_sha256'],('corpus SHA',x['path'])
  assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']==blobs[x['path']]['sha'],('Git position',x['path'])
  pdfs+=x['kind']=='outside_pdf'
  for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
   for k,r in patterns.items():
    mm=list(r.finditer(line))
    if mm:computed[k].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
 assert pdfs==776
 for lex in lexical:
  for k,result in lex['results'].items():assert computed[k]==result,('lexical membership/multiset',k)
 ts=data(OLD[1]/'title-screen.json');assert ts['titles']==sorted({x['path'].split('/')[1] for x in domain if re.search(ts['expression'],x['path'].split('/')[1])})
 passages=0
 for manifest in [old/'read-manifest.json' for old in OLD]+[S/'read-manifest.json']:
  for p in data(manifest)['passages']:
   b=read(p['local']);assert sha(b)==p['file_sha256'],('passage file',p['local']);t=b.decode();ls=t.splitlines() if p['convention']=='splitlines' else t.split('\n')
   assert 1<=p['start']<=p['end']<=len(ls)
   part='\n'.join(ls[p['start']-1:p['end']]);assert sha(part.encode())==p['passage_sha256']
   if 'passage' in p:assert part==p['passage']
   if 'line_count' in p:assert p['line_count']==len(ls)
   passages+=1
 for x in data(S/'retrieval.json'):
  if 'error' not in x:assert sha(read(x['path']))==x['sha256']
 assert data(S/'literature/upstream-head.json')['object']['sha']==PIN
 assert data(OLD[1]/'literature/head.json')['object']['sha']==PIN
 assert data(OLD[0]/'literature/upstream-head.json')['sha']==PIN
 # Only the two explicit selections; never rerun the inherited 776 PDF extractions.
 replay=data(S/'pdf-replay.json');assert len(replay)==2
 for x in replay:
  out=subprocess.run(['pdftotext','-layout',str(ROOT/x['pdf']),'-'],capture_output=True,check=True)
  assert out.stdout==read(x['text']),('selective PDF bytes',x['pdf'])
 # The entire immutable preflight has completed. Only now execute finite diagnostics.
 print('Immutable artifact, corpus, lexical, passage and selective PDF preflight: PASS',file=sys.stderr,flush=True)
 diag112=ROOT/'frontier/experiments/i112_inverse_boundary_discovery'
 diag115=ROOT/'frontier/experiments/i115_physical_elasticity_continuation'
 d112=runpy.run_path(str(diag112/'diagnostics.py'))['check']();assert d112==data(diag112/'diagnostic-result.json')
 d115=runpy.run_path(str(diag115/'diagnostics.py'))['check']();assert d115==data(diag115/'diagnostic-result.json')
 independent=runpy.run_path(str(E/'independent_diagnostics.py'))['check']();assert independent==data(E/'diagnostic-result.json')
 drift=[p for p in LEDGERS if sha(read(p))!=sha((S/'snapshots'/p).read_bytes())]
 print(json.dumps(dict(status='PASS',mode='preseal' if pre else 'sealed read-only',owned_files=len(actual),inherited_sealed_artifacts=inherited_count,immutable_direct_references=len(refs),original_blob_positions=len(domain),tree_entries=len(tree),manuscripts=749,inherited_pdf_text_bindings=pdfs,read_passages=passages,lexical_matched_lines={k:len(v) for k,v in computed.items()},selected_pdf_reextractions=len(replay),immutable_preflight_before_diagnostics=True,inherited_finite_diagnostics='I112 and I115 exact results reproduced once each; no recursive evidence verifier',independent_finite_diagnostics=independent,allowed_live_ledger_drift_observed=drift,scope='Evidence identity and specified finite algebra only; no universal proof, A*, P112, contribution, human-review or priority certification'),indent=2))
if __name__=='__main__':main()
