"""One-time preseal evidence preparation. Mutating; NOT the final verifier."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i115_physical_elasticity_continuation'
E=ROOT/'frontier/experiments/i115_physical_elasticity_continuation'
OLD=ROOT/'frontier/sources/i112_inverse_boundary_discovery'
assert not (S/'seal.json').exists()
def rel(p):return str(p.relative_to(ROOT))
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def put(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
# Bind the prior record directly, with no recursive verifier or corpus copying.
refs={x['path']:x['sha256'] for x in load(OLD/'immutable-references.json')}
refs.update(load(OLD/'seal.json')['sha256'])
refs[rel(OLD/'seal.json')]=sha((OLD/'seal.json').read_bytes())
assert refs[rel(OLD/'seal.json')]=='6b0e58e12bbc8af8e4ed3f66c7cb6d38963da6fce6370c4f3e840b91cae1a42e'
put(S/'immutable-references.json',[{'path':p,'sha256':h} for p,h in sorted(refs.items())])
D=load(OLD/'search-domain.json')
patterns={'physical_system':r'(?i)\b(?:Lam[eé]|elasticity|Runge|Carleman|traction)\b'}
results={k:[] for k in patterns}
for x in D:
 lines=(ROOT/x['local']).read_bytes().decode('utf-8',errors='replace').splitlines()
 for k,p in patterns.items():
  rr=re.compile(p)
  for i,line in enumerate(lines,1):
   mm=list(rr.finditer(line))
   if mm:results[k].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
put(S/'lexical-search.json',dict(patterns=patterns,results=results,scope='Exact full-domain lexical occurrences, not full semantic reading.'))
pat=r'(?i)(elastic|lame|calderon|boundary.*(metric|connection)|(metric|connection).*boundary|runge|unique.continuation)'
titles=sorted({x['path'].split('/')[1] for x in D if re.search(pat,x['path'].split('/')[1])})
put(S/'title-screen.json',dict(expression=pat,titles=titles,assessment='E/M/C full relevant proof operations read. Integrable metrics is projective divisor effectivity, screened by complete main.tex abstract; not an elasticity companion.'))
passages=[]
def passage(p,start=1,end=None,convention='splitlines',scope='complete file',url=None):
 b=p.read_bytes();t=b.decode('utf-8');lines=t.splitlines() if convention=='splitlines' else t.split('\n');end=len(lines) if end is None else end
 assert 1<=start<=end<=len(lines)
 excerpt='\n'.join(lines[start-1:end])
 passages.append(dict(local=rel(p),file_sha256=sha(b),start=start,end=end,line_count=len(lines),convention=convention,passage_sha256=sha(excerpt.encode()),scope=scope,url=url))
base=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints'
families={'E':'Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026','M':'Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026','C':'Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026'}
names={'E':['introduction','boundary-reduction','analytic-estimates','physical-amplitudes','transport-matching','coefficient-recovery'],'M':['01-introduction','02-boundary','03-product','04-spheres','05-angular','06-matrix','07-global'],'C':['01-introduction','06-bootstrap']}
for f,nn in names.items():
 for n in nn:
  p=base/families[f]/'build/sections'/(n+'.tex')
  passage(p,scope='Complete source section through ending; chunked reads where necessary',url='https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+str(p.relative_to(base.parent)))
p=base/'Integrable-metrics-and-effectivity-with-controlled-boundary-September-26-2026/build/source/main.tex'
passage(p,scope='Complete main file and abstract, contract-only false-positive screen; included sections NOT read')
for n,end,scope,url in [
 ('tan-v1.pdf.txt',965,'Complete main statements and Sections 2–3 proofs through analytic conclusion ending; references after line 965 not semantically read','https://arxiv.org/pdf/2211.06650v1'),
 ('ucp.pdf.txt',None,'Complete extracted preprint through references; final three-ball iteration referred out by authors, not rederived','https://arxiv.org/pdf/1005.3382v1')]:
 passage(S/'literature'/n,end=end,convention='LF',scope=scope,url=url)
for n,a,b,scope in [
 ('1708.06307v1.pdf.txt',1,None,'Complete extracted preprint through proofs and references'),
 ('1902.04838v2.pdf.txt',1,290,'Contract and physical boundary-condition definitions through selected lemma ending; remainder NOT fully read'),
 ('1708.00591v1.pdf.txt',181,231,'Theorem and remarks, contract-only screen; full proof NOT independently read in I115'),
 ('2609.20134v1.pdf.txt',1,212,'Complete main contract and scope ending, not a new full-proof read; inherited I112 proof passages retained separately')]:
 passage(OLD/'literature'/n,a,b,'LF',scope,'https://arxiv.org/pdf/'+n.split('.pdf')[0])
passage(S/'original-report-file.md',scope='Complete original I112 report; original-proof audit subject')
passage(ROOT/'AGENTS.md',scope='Complete governing instructions')
# Ledger snapshots are frozen in full. Only task-relevant current-status sections were semantically inspected.
put(S/'read-manifest.json',dict(passages=passages,ledger_read_scope='Full bytes frozen; current status and active-lane sections inspected. Oversized earlier output was truncated and is not counted as complete semantic ledger reading.',conventions='splitlines for corpus/TeX; LF for extracted PDFs; joined passage has no appended newline'))
put(S/'pdf-replay.json',[dict(pdf=rel(S/'literature'/n),text=rel(S/'literature'/(n+'.txt'))) for n in ['tan-v1.pdf','ucp.pdf']])
put(S/'failures.json',[
 dict(stage='context lookup',result='Invalid blank threadId in t3_thread_read; not used as evidence'),
 dict(stage='initial reads',result='Oversized ledger/source output truncated. Relevant source sections subsequently read in bounded complete chunks. Ledger claim restricted to inspected status sections.'),
 dict(stage='initial algebra probe',result="ModuleNotFoundError: No module named 'sympy'",disposition='Import failed before numerical result. Failed source not preserved; this failure record is retained. Replaced with standard-library Fraction arithmetic.'),
 dict(stage='Tan guessed version',url='https://arxiv.org/pdf/2211.06650v3',result='HTTP Error 404: Not Found',disposition='Observed metadata showed v1; v1 retrieved and used.'),
 dict(stage='physical Runge full primary proof',url='https://onlinelibrary.wiley.com/doi/10.1002/mma.70764',result='HTTP Error 403: Forbidden',disposition='No theorem or constants imported.'),
 dict(stage='late review read batching',result='Combined tool output truncated at aggregate token limit; report and CJLT contract reread individually. Not counted as a completed aggregate read.')])
put(S/'input-freeze.json',dict(full_task=rel(S/'supplied-task.txt'),parts=['original-brief.txt','original-report.txt','parent-response.txt'],markers=['--- ORIGINAL I112 BRIEF ---','--- ORIGINAL I112 REPORT ---','--- FINAL PARENT RESPONSE ---'],normalization='None: exact substrings, including delimiter-adjacent whitespace',on_disk_report=rel(S/'original-report-file.md')))
# Inventory is exact, including itself and the validation result that is written after preseal succeeds.
files={rel(p) for b in [S,E] for p in b.rglob('*') if p.is_file()}
files.update([rel(S/'inventory.json'),rel(E/'validation.json'),'frontier/iterations/i115-physical-elasticity-continuation.md'])
put(S/'inventory.json',dict(owned_paths=sorted(files),seal_path=rel(S/'seal.json'),selective_pdf_replay_limit=2,allowed_live_ledger_drift=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']))
print(json.dumps(dict(lexical_lines={k:len(v) for k,v in results.items()},read_passages=len(passages),immutable_references=len(refs),owned_before_seal=len(files))))
