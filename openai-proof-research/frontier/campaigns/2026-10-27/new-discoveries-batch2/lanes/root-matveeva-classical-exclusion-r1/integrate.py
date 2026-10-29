from pathlib import Path
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent; B=root.parents[1]; lanes=root.parent; repo=B.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((lanes/'root-fresh-source-r100-r101-handbacks/r100-freeze.json').read_text());candidate=Path(freeze['source_lane']);review=lanes/'sol-matveeva-classical-proof-review-r1'
for name,h in freeze['files'].items():
    assert sha(candidate/name)==h
    assert sha(review/'inputs/r100'/name)==h
count=0
for line in (review/'artifact-manifest.sha256').read_text().splitlines():
    h,name=line.split(maxsplit=1);assert sha(review/name.lstrip('*'))==h;count+=1
proof=(candidate/'PROOF.md').read_text()
old='Let H be any local nonzero solution of H\'=r*H. Then L(H)=0.'
new='Let H be a local nonzero solution of H\'=r*H, with its multiplicative constant to be normalized algebraically below. Then L(H)=0. The local singularity argument applies to any nonzero constant multiple; algebraicity over Qbar(x) is asserted only for an algebraically normalized branch.'
assert old in proof;proof=proof.replace(old,new)
old='is algebraic over Qbar(x). This is the rank-one argument also used in the q=0 branch.'
new='is algebraic over Qbar(x) when the multiplicative constant is chosen algebraic. The normalized branch H=x^rho*h with h(0)=1 used below is also algebraic: its normalizing constant is an algebraic value of the finite product of rational powers at the algebraic point zero after removal of x^rho. No claim is made for arbitrary transcendental constant multiples. This is the rank-one argument also used in the q=0 branch.'
assert old in proof;proof=proof.replace(old,new)
mark='The algebraic Laurent series 1/H(t^N) has only a finite pole'
assert mark in proof;proof=proof.replace(mark,'Here a globally bounded Laurent series means a Laurent series which becomes a globally bounded Taylor series after multiplication by a finite integral power of t; it does not mean applying the source Taylor-series definition to a pole. Finite shifts and rational principal-part subtraction preserve this property after a constant multiplier is allowed.\n\n'+mark)
(root/'PROOF-CLARIFIED.md').write_text('Root clarification of the frozen r100 proof after independent review. Only homogeneous-solution normalization and Laurent boundedness wording are clarified; frozen candidate bytes are preserved. No discovery credit.\n\n'+proof)
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'decision':'EXCLUDE_ROUTINE_CLASSICAL_REDUCTION','credit':0,'counts':[8,38],'ordinary_math':'PASS for the complete all-order source recurrence, with normalized homogeneous branch and explicit Laurent-boundedness convention','root_read':'Full independent review and candidate proof; actual Beukers G-function independence/minimal-equation theorem and Katz rational-local-exponent passage; actual Bostan-Caruso-Roques Proposition3.1 proof and Theorem5.6','bridge':'Affine rational ODE is the source generating-function translation. For nonrational S, q!=0 makes (S,Sprime) independent and its order2 annihilator minimal. Minimal-G theorem gives Fuchsian rational exponents; indicial factor (z-rho)(z-ord(q)-1) and rank-one criterion make normalized H algebraic. Rational ramification, Eisenstein denominator control and finite principal-part removal reduce S/H to exactly Andres integral primitive theorem. Rational and q=0 branches are separate.','strongest_countercase':'Full explicitly open all-order conjecture is resolved; the minimal-equation obstruction is a useful structural insight. Exclusion is based on a complete classical affine-ODE corollary plus the sources own primitive mechanism, not on brevity, worker self-exclusion or a claim that every classical-tool proof is ineligible.','corrections':['Arbitrary homogeneous solutions may have transcendental constants: use normalized algebraic H=x^rho h with h(0)=1.','Globally bounded Laurent means globally bounded after a finite monomial shift, then remove principal part before Andre.'],'corrected_copy':'PROOF-CLARIFIED.md','corrected_copy_sha256':sha(root/'PROOF-CLARIFIED.md'),'frozen_candidate_files':len(freeze['files']),'review_artifacts_verified':count,'independent_checks':'37 exact gauge, indicial and ramification bookkeeping checks; imported deep theorems are cited, not numerically verified','prior_root_checks':'90 exact recurrence-to-ODE coefficient identities','historical_novelty':'HOLD separately; no earlier printed exact full corollary asserted. Current public Matveeva artifact refutes a different parameter claim and does not resolve Conjecture4.1.','review_sha256':sha(review/'review.md'),'scope':'No Lean/paper/acceptance investment. Retain all source and registry qualifications.'}
(root/'EXCLUSION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';t=p.read_text().replace('independent Matveeva classical-proof review r1,','fresh structural/algebraic discovery r104,')
t=t.replace('r100 proposes the full Matveeva4.1 proof via G-functions and Andre; worker self-exclusion is pending independent review, not yet root-adopted.','r100 full Matveeva4.1 ordinary proof now PASS and EXCLUDED as a complete classical affine-ODE/G-function/Andre corollary after independent review and root primary-body inspection. Two normalization/Laurent wording corrections preserved in root-matveeva-classical-exclusion-r1/PROOF-CLARIFIED.md; frozen candidate unchanged. Historical novelty HOLD remains; no Lean/paper. See root-matveeva-classical-exclusion-r1/EXCLUSION.json.')
p.write_text(t)
paths=[p]
for folder in (root,review):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Adopt Matveeva classical exclusion with normalized proof clarification','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
