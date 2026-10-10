"""Preseal preparation only; final verifier never imports or calls this file."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i118_physical_quotient_angular';E=ROOT/'frontier/experiments/i118_physical_quotient_angular'
O=ROOT/'frontier/sources/i112_inverse_boundary_discovery';P=ROOT/'frontier/sources/i115_physical_elasticity_continuation'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return (ROOT/p).read_bytes()
def rel(p):return str(p.relative_to(ROOT))
def save(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
assert not (S/'seal.json').exists()
# Exact pieces of the supplied, frozen brief. No typography normalization.
t=(S/'supplied-task.txt').read_text();markers=['Original brief including all I112 materials:','Original I115 report in full:','Finalized parent response in full:'];names=['supplied-inherited-i112-materials.txt','supplied-original-i115-report.txt','supplied-finalized-parent-response.txt']
for i,n in enumerate(names):
 part=t.split(markers[i],1)[1]
 if i+1<len(markers):part=part.split(markers[i+1],1)[0]
 (S/n).write_text(part)
save(S/'input-freeze.json',dict(task=rel(S/'supplied-task.txt'),markers=markers,parts=names,original_report='frontier/iterations/i115-physical-elasticity-continuation.md',parent='frontier/experiments/i115-parent-verification.json'))
refs={}
for old in [O,P]:
 for x in json.loads((old/'immutable-references.json').read_text()):
  assert sha(read(x['path']))==x['sha256'];refs[x['path']]=x['sha256']
 for n in ['seal.json','inventory.json']:refs[rel(old/n)]=sha((old/n).read_bytes())
for p in ['frontier/iterations/i115-physical-elasticity-continuation.md','frontier/experiments/i115-parent-verification.json','frontier/experiments/i112-parent-verification.json','sources/CONTENTS.md']:
 refs[p]=sha(read(p))
# Prior inventories are bound and verified flat, including their immutable originals.
save(S/'immutable-references.json',[dict(path=p,sha256=h) for p,h in sorted(refs.items())])
base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
m=base+'Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026/build/sections/'
e=base+'Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/build/sections/'
c=base+'Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/build/sections/'
passages=[]
def passage(p,start=1,end=None,conv='splitlines',scope='Complete file through ending'):
 b=read(p);ls=b.decode().splitlines() if conv=='splitlines' else b.decode().split('\n');end=end or len(ls)
 passages.append(dict(local=p,file_sha256=sha(b),start=start,end=end,line_count=len(ls),convention=conv,passage_sha256=sha('\n'.join(ls[start-1:end]).encode()),scope=scope,url=('https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+p.split('/corpus/',1)[1]) if '/corpus/' in p else None))
for n in ['01-introduction.tex','02-boundary.tex','03-product.tex','04-spheres.tex','05-angular.tex','06-matrix.tex','07-global.tex']:passage(m+n)
for n in ['introduction.tex','boundary-reduction.tex']:passage(e+n)
passage(e+'analytic-estimates.tex',1,115,scope='Complete augmentation lemma and proof; later Carleman operations inherited, not newly fully read')
passage(c+'06-bootstrap.tex')
passage('frontier/sources/i115_physical_elasticity_continuation/literature/tan-v1.pdf.txt',1,965,'LF','All main statements, symbol recursion, boundary recovery, analytic conclusion through proof ending')
passage(rel(S/'literature/hardy-v1.pdf.txt'),1,135,'LF','Contract and beginning of definitions; not complete paper')
passage(rel(S/'literature/hardy-v1.pdf.txt'),333,640,'LF','Complete Section 4 through ending, followed by initial Section 5 definitions; later decomposition not relied on')
passage(rel(S/'literature/hardy-v1.pdf.txt'),1065,1287,'LF','Complete appendix through ending; kernel estimates and projection proof; no claim of full-paper read')
passage('frontier/iterations/i115-physical-elasticity-continuation.md')
passage('AGENTS.md')
for p in ['frontier/experiments/i115_physical_elasticity_continuation/verify.py','frontier/experiments/i115_physical_elasticity_continuation/diagnostics.py','frontier/experiments/i115_physical_elasticity_continuation/moment_probe.py']:passage(p)
save(S/'read-manifest.json',dict(passages=passages,ledger_scope='Full bytes frozen; current status, accepted count, I112/I115 and other active-lane status sections inspected. Oversized initial ledger/catalogue output was truncated and is not a full semantic read.',convention='TeX/corpus str.splitlines(); PDF LF splitting preserves form feeds. Joined passages have no appended newline.'))
# Flat lexical screen with explicit member paths and match multiplicities.
pat=r'(?i)(?:elastic|Lam[eé]|physical).{0,100}(?:quotient|angular|sphere|trace)|(?:quotient|angular|sphere).{0,100}(?:elastic|Lam[eé]|physical)'
r=re.compile(pat);hits=[];domain=json.loads((O/'search-domain.json').read_text())
for x in domain:
 for i,line in enumerate(read(x['local']).decode('utf-8',errors='replace').splitlines(),1):
  mm=list(r.finditer(line))
  if mm:hits.append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(z.span()) for z in mm]))
save(S/'lexical-search.json',dict(patterns=dict(physical_quotient=pat),results=dict(physical_quotient=hits),scope='Full-domain lexical membership and occurrences; not full semantic reading'))
save(S/'pdf-replay.json',[dict(pdf='frontier/sources/i115_physical_elasticity_continuation/literature/tan-v1.pdf',text='frontier/sources/i115_physical_elasticity_continuation/literature/tan-v1.pdf.txt'),dict(pdf=rel(S/'literature/hardy-v1.pdf'),text=rel(S/'literature/hardy-v1.pdf.txt'))])
save(S/'failures.json',dict(inherited='All I112/I115 failures retained byte-for-byte under their directly verified seals, including the two mathematical scope failures. No repaired original is relabelled PASS.',current=[dict(kind='read output truncation',detail='Initial combined ledgers/catalogue read exceeded output budget; only later targeted status/catalogue reads counted. A combined original-report/web result was also truncated at aggregate display; report tail 280-335 was reread explicitly; supplied original is fully available and frozen.'),dict(kind='method obstruction',detail='Physical frozen normal trace has a nonzero nilpotent principal correction; scalar lower-order comparison and positive Hermitian symmetrization of that trace fail. This is not an inverse-pair counterexample.')]))
print(json.dumps(dict(read_passages=len(passages),new_lexical_matched_lines=len(hits),immutable_direct_references=len(refs))))
