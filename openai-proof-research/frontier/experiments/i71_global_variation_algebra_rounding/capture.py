"""One-shot I71 evidence bindings; does not modify any prior file."""
from pathlib import Path
import json,hashlib,subprocess,sys,platform,re
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i71_global_variation_algebra_rounding'
P=S/'primary'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(name,x):
 p=S/name
 if p.exists():raise RuntimeError('Refusing overwrite: '+str(p))
 p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
extra=['frontier/iterations/i65-linked-symmetric-algebra-rounding.md','frontier/iterations/i61-averaged-entropy-coefficient-rounding.md','frontier/findings/R014-uniform-coefficient-extraction.md']
dump('additional-references.json',[dict(path=p,sha256=sha((R/p).read_bytes()),mutable=False) for p in extra])
old=json.loads((R/'frontier/sources/i69_global_algebra_rounding_budget/passages.json').read_bytes())
passages=[]
def passage(p,a,b,kind):
 p=Path(p);body=p.read_bytes();piece=b''.join(body.splitlines(keepends=True)[a-1:b])
 passages.append(dict(path=str(p.relative_to(R)),first_line=a,last_line=b,file_sha256=sha(body),passage_sha256=sha(piece),scope=kind))
for idx in [0,7]:
 rec=old[idx];passage(R/rec['path'],rec['first_line'],rec['last_line'],'Actual pinned operation read in I71; bytes hash-referenced')
for name,ranges in {
 'bk':[(90,150),(345,485)],
 'li':[(1,100),(430,492),(510,590)],
 'hamiltonian':[(1,36),(370,475),(1530,1660)],
 'fox':[(530,650)],
 'auddy':[(890,943),(2225,2300)]}.items():
 for a,b in ranges:passage(P/(name+'.txt'),a,b,'Selected actual statement/proof passage, not full-paper certification')
dump('passages.json',passages)
versions=[]
for name in ['bk','li','hamiltonian','fox','auddy']:
 p=P/(name+'.txt');s=p.read_text()
 versions.append(dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()),served_markers=re.findall(r'arXiv:\s*[^\s\[]+',s[:5000]),first_lines=s.splitlines()[:25]))
dump('versions.json',versions)
corpus='frontier/sources/i14_spectral_width_novelty_r3/corpus'
searches=[]
for name,pattern in [('variation',r'global maxim|simultaneous variation|Riemannian Hessian|strict local maxim'),('cuts',r'spectral partition|spectral cut|pinching|almost.commuting'),('linked',r'Frobenius algebra|orthogonally decomposable|simplicial algebra')]:
 p=subprocess.run(['rg','--no-ignore','-n',pattern,corpus],cwd=R,capture_output=True,text=True)
 dump(name+'-search.json',p.stdout.splitlines())
 searches.append(dict(name=name,pattern=pattern,returncode=p.returncode,stderr=p.stderr,count=len(p.stdout.splitlines())))
dump('searches.json',searches)
dump('read-contracts.json',dict(
 full=['AGENTS.md','frontier/iterations/i69-global-algebra-rounding-budget.md','frontier/experiments/i69_global_algebra_rounding_budget/verify.py','frontier/iterations/i65-linked-symmetric-algebra-rounding.md','frontier/findings/R014-uniform-coefficient-extraction.md',str((S/'brief.txt').relative_to(R))],
 selected=[dict(path='frontier/iterations/i61-averaged-entropy-coefficient-rounding.md',lines='280-383'),dict(path='four current ledgers',scope='current statuses and acceptance boundaries; entire bytes frozen, not full historical-line re-audit')],
 source_passages='passages.json',prior_interfaces='I69 inputs/read-contracts/pins/passages/prior-hashes/seal/verification, hash-referenced; inherited full-proof claims not re-certified',
 corpus_scope='Exact fixed 9340-file domain, not all 10373 blobs; unchanged I69 verifier replays inventory, Git blobs and 1033 outside entries.',
 discovery_limit='No claim of exhaustive literature reading or worldwide priority.'))
dump('failures-and-limits.json',[
 dict(operation='optional dependency inspection',result="ModuleNotFoundError: No module named 'numpy'",response='No installation; independent diagnostics use only standard library.'),
 dict(operation='early broad discovery displays',result='Output truncation retained in initial-failures; earliest web batch not separately archived.',response='No proof or read claim depends on omitted output; actual primary responses acquired separately.'),
 dict(operation='Hamiltonian version comparison',result='Search-index abstract displayed exponent 1/6; fresh PDF is v3 with exponent 1/3.',response='Use v3 actual statement and proof scope; preserve older search response.'),
 dict(operation='fresh HTTP acquisition',result='All ten requests successful; no HTTP failure omitted.'),
 dict(operation='analytic target',result='AR_K and exact-B=I AR unproved and unrefuted.',response='No nomination/count change; local and nonlinked obstructions do not refute target.')])
dump('analytic-verdicts.json',dict(
 input_original_pass=['linkage as used','arbitrary-normalization scalar sign rounding','Walsh/simplicial identification as used','supplied codimension rounding as used'],
 not_independently_reaudited_or_used=['I69 combined greedy residual identity','I69 arbitrary multiscale supplied-block result','I69 scalar unitalization'],
 new_author_proofs=['strict poor local maxima at exact B=I with normalized E tending to zero and bounded global cost','full covariance and finite-comparison identities','common-cut aggregate estimate and full-slot cap preservation','global refinement bookkeeping and terminal certificate','nonlinked real X/Z aggregate-rounding obstruction'],
 open=['global-maximizer finite-comparison entrance','linked cumulative spectral-loss/stopping inequality','AR_K','new capped entropy conclusion'],
 evidence_not_proof=True,nomination=False))
p=subprocess.run(['pdftotext','-v'],capture_output=True,text=True)
dump('environment.json',dict(python=sys.version,platform=platform.platform(),pdftotext_stdout=p.stdout,pdftotext_stderr=p.stderr,pdftotext_status=p.returncode))
print(json.dumps(dict(passages=len(passages),searches=searches,versions=versions),indent=2))
