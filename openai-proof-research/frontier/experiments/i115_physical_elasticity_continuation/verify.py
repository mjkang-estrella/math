"""I115 offline READ-ONLY final verifier. No downloads/writes/bytecode/repair/reseal.
Run python3 -B verify.py; --preseal is available only before a seal exists.
Checks bytes, exact lexical occurrences, selected PDF extractions and finite algebra.
Does NOT certify universal proofs or contributions; never invokes earlier verifiers.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,re,subprocess,runpy
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i115_physical_elasticity_continuation'
E=ROOT/'frontier/experiments/i115_physical_elasticity_continuation'
OLD=ROOT/'frontier/sources/i112_inverse_boundary_discovery'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def rel(p):return str(p.relative_to(ROOT))
def read(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def data(p):return json.loads(p.read_text())
def main():
 pre=sys.argv[1:]==['--preseal'];assert not sys.argv[1:] or pre
 inv=data(S/'inventory.json');expected=set(inv['owned_paths']);sealpath=inv['seal_path']
 actual={rel(p) for b in [S,E] for p in b.rglob('*') if p.is_file()}
 actual.add('frontier/iterations/i115-physical-elasticity-continuation.md')
 validation=rel(E/'validation.json')
 if pre:
  assert not (ROOT/sealpath).exists(),'preseal forbidden after seal'
  if validation not in actual:expected.remove(validation)
  assert actual==expected,dict(extra=sorted(actual-expected),missing=sorted(expected-actual))
 else:
  assert actual==expected|{sealpath},dict(extra=sorted(actual-expected-{sealpath}),missing=sorted(expected-actual))
  sealed=data(ROOT/sealpath);assert set(sealed['sha256'])==expected
  for p,h in sealed['sha256'].items():assert sha(read(p))==h,('owned',p)
  val=data(E/'validation.json');assert val['status']=='PASS' and val['exit_code']==0
 refs=data(S/'immutable-references.json')
 for x in refs:assert sha(read(x['path']))==x['sha256'],('immutable',x['path'])
 # Directly verify the prior seal and its complete inventory, no prior verifier execution.
 assert sha((OLD/'seal.json').read_bytes())=='6b0e58e12bbc8af8e4ed3f66c7cb6d38963da6fce6370c4f3e840b91cae1a42e'
 oldseal=data(OLD/'seal.json');oldinv=data(OLD/'inventory.json')
 assert set(oldseal['sha256'])==set(oldinv['owned_paths'])
 for p,h in oldseal['sha256'].items():assert sha(read(p))==h,('I112 seal',p)
 # Exact supplied originals retain their delimiter-adjacent whitespace.
 freeze=data(S/'input-freeze.json');task=read(freeze['full_task']).decode('utf-8');markers=freeze['markers']
 for i,n in enumerate(freeze['parts']):
  part=task.split(markers[i],1)[1]
  if i+1<len(markers):part=part.split(markers[i+1],1)[0]
  assert part.encode()==(S/n).read_bytes(),('supplied verbatim',n)
 assert read(freeze['on_disk_report'])==read('frontier/iterations/i112-inverse-boundary-discovery.md')
 parent=json.loads((S/'parent-response.txt').read_text());assert parent['seal_sha256']==sha((OLD/'seal.json').read_bytes())
 for x in parent['parent_reading']['complete_files']:assert sha(read(x['path']))==x['sha256']
 for x in parent['parent_reading']['passages']:
  b=read(x['path']);assert sha(b)==x['source_sha256'];part='\n'.join(b.decode().splitlines()[x['start']-1:x['end']]);assert sha(part.encode())==x['passage_sha256']
 # One nonrecursive original-corpus pass, preserving lexical line conventions.
 domain=data(OLD/'search-domain.json');tree=data(OLD/'snapshots/sources/preprints-tree.json')['tree']
 blobs={x['path']:x for x in tree if x['type']=='blob'}
 assert len(tree)==13223 and len(blobs)==10373 and sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)==749
 assert len(domain)==10373 and {x['path'] for x in domain}==set(blobs)
 oldlex=data(OLD/'lexical-search.json');newlex=data(S/'lexical-search.json');patterns={**oldlex['patterns'],**newlex['patterns']};assert len(patterns)==len(oldlex['patterns'])+len(newlex['patterns'])
 rr={k:re.compile(p) for k,p in patterns.items()};computed={k:[] for k in patterns};pdfs=0
 for x in domain:
  b=read(x['local']);o=b if x['local']==x['original_local'] else read(x['original_local'])
  assert sha(b)==x['sha256'] and sha(o)==x['original_sha256'],('corpus SHA',x['path'])
  assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']==blobs[x['path']]['sha'],('git',x['path'])
  pdfs+=x['kind']=='outside_pdf'
  for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
   for k,r in rr.items():
    mm=list(r.finditer(line))
    if mm:computed[k].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
 assert pdfs==776
 for lex in [oldlex,newlex]:
  for k,result in lex['results'].items():assert computed[k]==result,('exact lexical occurrences',k)
 ts=data(S/'title-screen.json')
 assert ts['titles']==sorted({x['path'].split('/')[1] for x in domain if re.search(ts['expression'],x['path'].split('/')[1])})
 # Passage hashes are source identity, not claims that a machine semantically read proofs.
 allpass=[]
 for manifest in [OLD/'read-manifest.json',S/'read-manifest.json']:
  pp=data(manifest)['passages'];allpass+=pp
  for p in pp:
   b=read(p['local']);assert sha(b)==p['file_sha256'];t=b.decode('utf-8');lines=t.splitlines() if p['convention']=='splitlines' else t.split('\n')
   assert 1<=p['start']<=p['end']<=len(lines)
   excerpt='\n'.join(lines[p['start']-1:p['end']]);assert sha(excerpt.encode())==p['passage_sha256']
   if 'passage' in p:assert excerpt==p['passage']
   if 'line_count' in p:assert p['line_count']==len(lines)
 # Strictly selective new PDF extraction, to stdout only. Never re-extract inherited 776 texts.
 replay=data(S/'pdf-replay.json');assert len(replay)==inv['selective_pdf_replay_limit']==2
 for x in replay:
  out=subprocess.run(['pdftotext','-layout',str(ROOT/x['pdf']),'-'],capture_output=True,check=True)
  assert out.stdout==read(x['text']),('new PDF extraction',x['pdf'])
 for x in data(S/'retrieval.json'):
  if 'error' in x:continue
  p=x.get('file') or rel(S/'literature'/x['name']);assert sha(read(p))==x['sha256']
 assert data(S/'literature/head.json')['object']['sha']==PIN
 # Two standalone finite-algebra routines, not evidence workflows.
 original=runpy.run_path(str(ROOT/'frontier/experiments/i112_inverse_boundary_discovery/diagnostics.py'))['check']()
 assert original==data(ROOT/'frontier/experiments/i112_inverse_boundary_discovery/diagnostic-result.json')
 finite=runpy.run_path(str(E/'diagnostics.py'))['check']();assert finite==data(E/'diagnostic-result.json')
 # Four live ledgers alone may drift; their snapshots remain sealed owned files.
 drift=[]
 assert inv['allowed_live_ledger_drift']==['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
 for p in inv['allowed_live_ledger_drift']:
  if sha(read(p))!=sha((S/'snapshots'/p).read_bytes()):drift.append(p)
 result=dict(status='PASS',mode='preseal' if pre else 'sealed read-only',owned_files=len(actual),original_blob_positions=len(domain),manuscripts=749,tree_entries=len(tree),inherited_pdf_text_bindings=pdfs,immutable_references=len(refs),inherited_read_passages=len(data(OLD/'read-manifest.json')['passages']),new_read_passages=len(data(S/'read-manifest.json')['passages']),lexical_matched_lines={k:len(v) for k,v in computed.items()},selected_new_pdf_reextractions=len(replay),allowed_live_ledger_drift_observed=drift,original_finite_diagnostics=original,new_finite_diagnostics={k:v for k,v in finite.items() if k!='certificate'},degree_four_certificate={k:v for k,v in finite['certificate'].items() if k!='row_indices'},scope='Evidence identity and specified exact finite algebra only; not universal proof, substantiality, human review or priority certification')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
