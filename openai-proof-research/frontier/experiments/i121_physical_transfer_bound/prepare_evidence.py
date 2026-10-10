"""Preparation before validation/seal only. Never imported by final verifier."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i121_physical_transfer_bound';E=ROOT/'frontier/experiments/i121_physical_transfer_bound'
OLD=[ROOT/'frontier/sources'/n for n in ['i112_inverse_boundary_discovery','i115_physical_elasticity_continuation','i118_physical_quotient_angular']]
LEDGERS=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return (ROOT/p).read_bytes()
def rel(p):return str(p.relative_to(ROOT))
def data(p):return json.loads(p.read_text())
def save(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
assert not (S/'seal.json').exists()
for p in LEDGERS+['AGENTS.md']:
 q=S/'snapshots'/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(read(p))
t=data(S/'i121-task-snapshot.json')['brief'];(S/'supplied-task.txt').write_text(t)
markers=['--- ORIGINAL DIRECT I118 BRIEF ---','--- FULL RECURSIVE ORIGINAL RECORD (REQUIRED READ) ---','--- ORIGINAL I118 REPORT ---','--- FINALIZED PARENT RESPONSE ---']
parts=['supplied-direct-i118-brief.txt','supplied-recursive-record-instruction.txt','supplied-original-i118-report.txt','supplied-finalized-i118-parent-response.txt']
for i,n in enumerate(parts):
 p=t.split(markers[i],1)[1]
 if i+1<len(parts):p=p.split(markers[i+1],1)[0]
 (S/n).write_text(p)
save(S/'input-freeze.json',dict(markers=markers,parts=parts,task=rel(S/'supplied-task.txt'),original_i118_task_sha256='19806b3abe8937dbeb11fc72a8cb47a0c52d7bf2e7cee0a0880eefc2b5b2dbf1',normalization='None for stored exact substrings; report equality checked after removing delimiter-adjacent whitespace only'))
refs={}
for old in OLD:
 for x in data(old/'immutable-references.json'):
  assert sha(read(x['path']))==x['sha256'];refs[x['path']]=x['sha256']
 for n in ['inventory.json','seal.json']:refs[rel(old/n)]=sha((old/n).read_bytes())
for p in ['frontier/iterations/i118-physical-quotient-angular.md','frontier/experiments/i118-parent-verification.json','sources/CONTENTS.md','AGENTS.md','sources/upstream.json']:
 refs[p]=sha(read(p))
save(S/'immutable-references.json',[dict(path=p,sha256=h) for p,h in sorted(refs.items())])
base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
m=base+'Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026/build/sections/'
e=base+'Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/build/sections/'
c=base+'Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/'
passages=[]
def passage(p,conv='splitlines',scope='Complete file through ending'):
 b=read(p);ls=b.decode().splitlines() if conv=='splitlines' else b.decode().split('\n')
 passages.append(dict(local=p,file_sha256=sha(b),start=1,end=len(ls),line_count=len(ls),convention=conv,passage_sha256=sha('\n'.join(ls).encode()),scope=scope))
for n in ['01-introduction.tex','02-boundary.tex','03-product.tex','04-spheres.tex','05-angular.tex','06-matrix.tex','07-global.tex']:passage(m+n)
for n in ['introduction.tex','boundary-reduction.tex','analytic-estimates.tex']:passage(e+n)
passage(c+'06-bootstrap.tex')
passage('frontier/sources/i118_physical_quotient_angular/literature/hardy-v1.pdf.txt','LF','Complete paper; initial combined late-section display truncated; entire appendix recovered separately')
for p in [rel(S/'original-i118-brief.txt'),'frontier/iterations/i118-physical-quotient-angular.md','frontier/experiments/i118_physical_quotient_angular/verify.py','frontier/experiments/i118_physical_quotient_angular/prepare_evidence.py','frontier/experiments/i118_physical_quotient_angular/independent_diagnostics.py','AGENTS.md']:passage(p)
save(S/'read-manifest.json',dict(passages=passages,scope='Recorded complete semantic reads; source catalogue introduction and primary metadata contracts separately screened. Other inherited readings retained under their original scopes.',convention='str.splitlines for TeX/corpus; LF for PDF, preserving form feeds; no appended newline in passage hashes'))
pat=r'(?i)(?:elastic|Lam[eé]|physical).{0,120}(?:flux|nonnormal|non.normal|transfer|commutator)|(?:flux|nonnormal|non.normal|transfer|commutator).{0,120}(?:elastic|Lam[eé]|physical)'
r=re.compile(pat);hits=[]
for x in data(OLD[0]/'search-domain.json'):
 for i,line in enumerate(read(x['local']).decode('utf-8',errors='replace').splitlines(),1):
  mm=list(r.finditer(line))
  if mm:hits.append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(z.span()) for z in mm]))
save(S/'lexical-search.json',dict(patterns=dict(physical_transfer=pat),results=dict(physical_transfer=hits),scope='Full-domain lexical occurrences, not semantic reading'))
save(S/'pdf-replay.json',data(OLD[2]/'pdf-replay.json'))
save(S/'literature-screen.json',dict(queries=['Lamé system partial boundary data both coefficients arbitrary patch uniqueness Poisson kernel nonnormal 2026','site.arxiv.org 2510.10798 Hardy spaces Lamé equation','site.arxiv.org 2211.06650 elastic Dirichlet Neumann'],primary_observations=[{'url':'https://arxiv.org/abs/2510.10798','version':'v1','use':'complete inherited PDF read; independently derived frozen formulas only'},{'url':'https://arxiv.org/abs/2211.06650','version':'v1','use':'current metadata; complete proof inherited'},{'url':'https://arxiv.org/abs/2609.20134','version':'v1','use':'current contract only; no new theorem imported'}],limits='Bounded primary-source screen; no worldwide priority, exhaustive search or absence theorem'))
save(S/'failures.json',dict(inherited='Every I112/I115/I118 failure artifact and mathematical failure is preserved under its original seal and verified directly.',current=[dict(kind='combined output truncation',detail='Combined Hardy tail and web page output exceeded aggregate tool output budget; the complete Hardy appendix was reread separately before recording its full reading.'),dict(kind='analytic blockage',detail='Nonnormal accretivity and exact quotient compression do not pay coupled principal commutators or physical r^-1 terms.'),dict(kind='analytic blockage',detail='Actual flux Cauchy defect lacks a uniform seed-to-core estimate; multipole tests omit the lower seed and are not P112 counterpairs.')]))
print(json.dumps(dict(new_passages=len(passages),new_lexical_lines=len(hits),references=len(refs))))
