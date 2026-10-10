"""Preparation only, never called by final verifier; writes only owned I99 artifacts."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path.cwd()
S=Path('frontier/sources/i99_quantitative_arithmetic_patterns_discovery')
E=Path('frontier/experiments/i99_quantitative_arithmetic_patterns_discovery')
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
domain=json.loads((S/'search-domain.json').read_text())
by_path={r['path']:r for r in domain}
selected=[]
def add(prefix,tail,start=1,end=None,note=''):
 row=next(x for x in domain if x['path'].split('/')[1].startswith(prefix) and x['path'].endswith(tail))
 b=Path(row['local']).read_bytes();lines=b.decode().split('\n')
 if lines[-1]=='':lines.pop()
 if end is None:end=len(lines)
 assert 1<=start<=end<=len(lines),(row['path'],len(lines),start,end)
 excerpt='\n'.join(lines[start-1:end])
 selected.append(dict(path=row['path'],local=row['local'],url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+row['path'],git_sha=row['git_sha'],sha256=sha(b),line_convention='LF; terminal empty element omitted',start=start,end=end,total_lf_lines=len(lines),excerpt=excerpt,excerpt_sha256=sha(excerpt.encode()),note=note))
add('A-power-saving-for-intersective','sections/introduction.tex',note='complete statement and method contract')
add('A-power-saving-for-intersective','sections/kernel.tex',note='complete kernel proof through ending')
add('A-power-saving-for-intersective','sections/tuples.tex',note='complete tuple construction, mixing, covariance, threshold through ending')
add('A-Power-Saving-for-Polynomial','sections/introduction.tex',note='complete statement, assumptions, dependency contract')
add('A-Power-Saving-for-Polynomial','sections/kernel.tex',note='complete prime kernel, all errors, pair cancellation through ending')
add('Quasipolynomial-Bounds','sections/00-introduction.tex',note='complete statement and lower-operation roadmap')
add('Quasipolynomial-Bounds','sections/01-setup.tex',end=235,note='triangular rule and complete ap:absolute proof')
add('Squarefree-values','sections/01-introduction.tex',note='complete statements incl explicit simultaneous corollary')
add('Squarefree-values','sections/02-sieve.tex',note='complete sieve transfer, contents and simultaneous family proof')
add('the-additive-indecomposability','sections/01-introduction.tex',note='complete main contract and roadmap')
add('the-additive-indecomposability','sections/02-preliminaries.tex',end=140,note='complete fixed-shift and finite-factor proofs, two-infinite-set contract')
add('the-additive-indecomposability','sections/09-conclusion.tex',note='complete terminal symmetrization, exact hypothesis scope')
add('A-power-saving-for-square-difference','sections/introduction.tex',end=165,note='stronger-generalization predecessor statement and method')
add('Quantitative-Superexponential','sections/01-introduction.tex',end=120,note='coloring companion statement; not a nonlinear-pattern input')
dump(S/'passages.json',selected)
contracts=[
 {'key':'AP','labels':['ap:main','ap:increment','ap:absolute'],'parameters':'fixed k; coefficients of cells unrestricted; progression-free support required','used_for':'screen and failed shortcut only'},
 {'key':'IP','labels':['thm:main','tuple:laws','tuple:conditional-mixing','tuple:covariance','kernel:estimate','kernel:comparison','kernel:coefficients'],'parameters':'c_k degree-only; C_h,N_h coefficient-dependent; integer argument; one pair; all-coordinate mixing','used_for':'B2 scalar independence input and Route A operation comparison'},
 {'key':'PP','labels':['thm:main','prop:pair-cancellation','lem:kernel-comparison'],'parameters':'unit roots; c_h,C_h polynomial-dependent; prime argument; two-endpoint kernel','used_for':'screen only; no new prime theorem'},
 {'key':'SF','labels':['thm:density','cor:separable-products','prop:sieve-transfer'],'parameters':'fixed finite family, separable; factor degrees <=k+2; exact joint local admissibility; no height-uniform error','used_for':'explicit duplicate screen'},
 {'key':'OI','labels':['cor:ostmann','thm:main','lem:shifted-sieve','lem:finite-factor'],'parameters':'eventual equality, both coverage and no composites; not approximate-density coverage','used_for':'scope screen only'},
 {'key':'PP2021','url':'https://arxiv.org/abs/2003.04122v2','read':'Theorems 1.1,1.2,1.5; sections 2-7 and their endings','used_for':'existing local/major-arc/increment operations; no claim of independent audit'},
 {'key':'SW2025','url':'https://arxiv.org/abs/2505.16822v2','read':'Theorems 1.1-1.3,2.4; complete section 4','used_for':'current stronger distinct-degree companion and iteration contract'},
 {'key':'AS2025','url':'https://arxiv.org/abs/2506.13010v1','read':'Theorems 1.1,1.6; complete Lemma 2.11 and section 2.4 terminal deduction','used_for':'strongest inspected polynomial-common-difference transfer; other supporting lemmas not audited'}]
dump(S/'source-contracts.json',contracts)
refs=[]
mutable=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
for name in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json']+mutable:
 snap=S/'snapshots'/name
 refs.append(dict(path=name,sha256=sha(snap.read_bytes()),snapshot=str(snap),may_drift=name in mutable))
dump(S/'references.json',refs)
pdfs=[]
for row in domain:
 if row['kind']=='outside_pdf' and any(row['path'].split('/')[1].startswith(x) for x in ['A-power-saving-for-intersective','A-Power-Saving-for-Polynomial','Squarefree-values-of-quartics']):
  b=subprocess.run(['pdftotext','-layout',row['original_local'],'-'],stdout=subprocess.PIPE,check=True).stdout
  assert sha(b)==row['sha256']
  pdfs.append(dict(original=row['original_local'],text=row['local'],sha256=sha(b),method=['pdftotext','-layout','{original}','-'],scope='one of exactly three pinned PDF re-extractions'))
p=S/'literature'
b=subprocess.run(['pdftotext','-layout',str(p/'peluse-prendiville.pdf'),'-'],stdout=subprocess.PIPE,check=True).stdout
assert b==(p/'peluse-prendiville.txt').read_bytes()
pdfs.append(dict(original=str(p/'peluse-prendiville.pdf'),text=str(p/'peluse-prendiville.txt'),sha256=sha(b),method=['pdftotext','-layout','{original}','-'],scope='downloaded primary PDF only'))
dump(S/'pdf-replay.json',pdfs)
# Local extraction/version evidence, with exact bytes and both line conventions.
lit=[]
for file in sorted(p.glob('*.txt')):
 b=file.read_bytes();t=b.decode()
 lit.append(dict(path=str(file),sha256=sha(b),lf_lines=len(t.split('\n'))-(t.endswith('\n')),splitlines_count=len(t.splitlines())))
dump(S/'literature-texts.json',lit)
ns={'__name__':'i99_exact_diagnostics'}
exec(compile((E/'diagnostics.py').read_bytes(),str(E/'diagnostics.py'),'exec'),ns)
dump(E/'diagnostics-result.json',ns['run']())
print(json.dumps({'passages':len(selected),'pdf_replays':len(pdfs),'references':len(refs),'domain':len(domain)}))
