"""Author-side preparation only. Never called by the read-only verifier."""
from pathlib import Path
import json,hashlib,re,subprocess
S=Path('frontier/sources/i138_nonlinear_dynamics_discovery')
X=Path('frontier/experiments/i138_nonlinear_dynamics_discovery')
assert not (S/'seal.json').exists()
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(Path(p).read_bytes())
def put(p,x):Path(p).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def row(p):b=Path(p).read_bytes();return dict(path=str(p),sha256=sha(b),bytes=len(b))
def inactive(p):assert not re.search(r'(?:^|/)(?:i|iteration)(?:136|137)(?:[-_/])',p),p
refs={}
def add(p,digest=None,size=None):
 p=str(p);inactive(p)
 if p in MUTABLE:return
 if p.startswith(str(S)+'/') or p.startswith(str(X)+'/'):return
 r=row(p)
 if digest is not None:assert r['sha256']==digest,p
 if size is not None:assert r['bytes']==size,p
 if p in refs:assert refs[p]==r
 refs[p]=r
names=['i114_quantum_information_discovery','i117_bosonic_entropy_stability','i120_thermal_trace_stability','i123_thermal_production_stability','i126_random_geometry_discovery','i129_disordered_fk_occupation','i132_discrete_probability_discovery','i135_complex_analysis_discovery']
packages=[]
for name in names:
 base=Path('frontier/sources')/name;p=base/'seal.json';z=load(p);add(p)
 if name.startswith('i135'):assert sha(p.read_bytes())=='5b655f088507e8a8d87e4919c91b199064f70b4cf8f681d8ab315eaf2b3b7cdf'
 reports=[r['path'] for r in z['files'] if r['path'].startswith('frontier/iterations/')]
 assert len(reports)==1
 packages.append(dict(source=str(base),experiment=str(Path('frontier/experiments')/name),report=reports[0],seal=row(p)))
 for r in z['files']:add(r['path'],r['sha256'],r.get('bytes'))
 for f in ('inputs.json','references.json'):
  if (base/f).exists():
   for r in load(base/f):
    if 'snapshot' in r:add(r['snapshot'],r['sha256'])
    if not r.get('mutable',False):add(r['path'],r['sha256'],r.get('bytes'))
 # Bind originals of snapshots, retaining only the same four live exceptions.
 if (base/'snapshots.json').exists():
  for r in load(base/'snapshots.json'):
   add(r['snapshot'],r['sha256'],r.get('bytes'))
   add(r['path'],r['sha256'],r.get('bytes'))
put(S/'inherited-packages.json',packages)
for r in load(S/'snapshots.json'):add(r['path'],r['sha256'],r.get('bytes'))
for label in ('source','overlap'):
 for p in load(S/(label+'-query.json'))['files']:add(p)
manifest=load(S/'read-manifest.json')
partial={0,2,4,11,19,26,41,42,43,59,60}
for i,r in enumerate(manifest):
 b=Path(r['path']).read_bytes();t=json.loads(b)[r['field']] if r['field'] else b.decode();ls=t.splitlines()
 r['ending']=ls[r['end']-1];r['display_status']='truncated-attempt' if i in partial else 'supplied'
 add(r['path'],r['sha256'])
put(S/'read-manifest.json',manifest)
chunks=load(S/'context-chunks.json')
for i,r in enumerate(chunks):
 text='\n'.join(Path(r['path']).read_text().splitlines()[r['line_start']-1:r['line_end']])
 assert text[r['char_start']:r['char_end']]==r['text']
 r.update(sha256=sha(Path(r['path']).read_bytes()),chunk_sha256=sha(r['text'].encode()),display_status='supplied-after-recovery' if i==4 else 'supplied',ending=r['text'][-120:])
put(S/'context-chunks.json',chunks)
# Match current direct user record to the immutable original report and receipt.
current=S/'snapshots/frontier/iterations/iteration138-nonlinear-dynamics-discovery-task.json';task=load(current)
t=task['brief'];report=t.split('--- FULL I135 REPORT ---\n',1)[1].split('\n--- FINALIZED I135 PARENT RESPONSE ---',1)[0]
assert report.strip()==Path('frontier/iterations/i135-complex-analysis-discovery.md').read_text().strip()
parent=json.loads(t.split('--- FINALIZED I135 PARENT RESPONSE ---\n',1)[1]);assert parent==load('frontier/experiments/i135-parent-verification.json')
put(S/'direct-context-binding.json',dict(task=row(current),report=row('frontier/iterations/i135-complex-analysis-discovery.md'),parent=row('frontier/experiments/i135-parent-verification.json'),supplied_in_user_message=True,all_other_fields={k:v for k,v in task.items() if k!='brief'}))
for p in ['frontier/sources/i114_quantum_information_discovery/search-domain.json','frontier/sources/i114_quantum_information_discovery/snapshots/sources/preprints-tree.json','frontier/sources/i114_quantum_information_discovery/corpus-rg-inventory.json','frontier/experiments/i114_quantum_information_discovery/html_text.py']:add(p)
# Per-file source citations use the unchanged original domain path.
domain=load('frontier/sources/i114_quantum_information_discovery/search-domain.json')
put(S/'source-bindings.json',[dict(path=r['path'],local=r['local'],sha256=r['sha256'],url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+r['path']) for r in domain if r['local'] in {x['path'] for x in manifest}])
put(S/'references.json',[refs[p] for p in sorted(refs)])
put(S/'failure-log.json',dict(scope='Acquisition/display limitations; not universal proof evidence',items=[
 'Initial broad filename inventory listed active I136/I137 snapshot names; no contents of those outputs were read or hashed. Frozen ledgers contain historical active-work mentions only.',
 'Original-context requested ranges 135:1-294,295-end;120:221-441;123:1-152;126:317-350 and317-338 had display truncations. Mathematical missing subranges were recovered before the audit; full escaped parent suffixes were read in fifteen character chunks. Chunk4 was resupplied after an outer truncation. Final evidence pass resupplied smaller ranges so complete coverage excludes every truncated-attempt record.',
 'Initial ledger displays and a later broad ledger-excerpt output truncated. The retained ledger excerpts are the subsequently displayed exact character windows, not claims of full historical reading.',
 'Billiard introduction.tex path failed because physical companion uses01-introduction.tex. Correct path then read. Initial rg ignored source paths; rg --files --no-ignore supplied their inventory.',
 'Combined I57/I58/billiard displays truncated. I58 fully resupplied, I57 contribution ending and physical theorem separately supplied; no claim of a new full I57 proof reading.',
 'Combined consensus PDF display truncated. Lemma14 and its ending and uniform-window discussion separately supplied; only stated scoped comparisons are relied on. PDF two-column layout is preserved and can interleave independent columns.',
 'Speculative consensus HTML2105.07183v4 returned404. The actual current version page saysv1, and its PDF was successfully retrieved. No failed body is mislabelled a full proof.',
 'Exploratory web searches included nonprimary/secondary hits and stale snippets. They were leads only, not retained proof premises. Current retained arXiv pages identify CNPv2,Craciunv3,consensusv1.',
 'No inherited diagnostics or PDF extractions are rerun. New pdftotext products are immutable byte bindings, not offline extractor reproductions.'
]))
version=subprocess.run(['pdftotext','-v'],capture_output=True,text=True)
put(S/'representations.json',dict(read_convention='UTF-8 splitlines inclusive; LF joined without appended LF; raw LF and terminal LF separately recorded. PDF form-feed is a splitlines separator.',pdf_extractor=version.stderr or version.stdout,pdf_extraction='pdftotext -layout input.pdf output.txt; exact bytes frozen; no offline subprocess or visual-layout assertion',html_converter=row('frontier/experiments/i114_quantum_information_discovery/html_text.py'),lexical_convention='Every re.finditer occurrence, repeated representations retained, zero-based codepoint offsets in each splitline; IGNORECASE; sorted fixed domains',external_scope='CNPv2 definition and Section6 proofs through ending; Craciunv3 embedding and Section8 application ending only; consensusv1 statement, uniform-window discussion, evolution Lemma14 through ending. No full external-proof audit claimed.'))
print('Prepared',len(refs),'flat references',len(packages),'original packages')
