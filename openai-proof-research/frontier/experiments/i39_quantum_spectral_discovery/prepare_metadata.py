"""One-time evidence metadata; refuses to run after the artifact freeze."""
from pathlib import Path
import json,hashlib,re,runpy
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i39_quantum_spectral_discovery';E=Path(__file__).parent
assert not (S/'artifact-seal.json').exists(), 'Never refresh a seal'
sha=lambda b:hashlib.sha256(b).hexdigest()
def write(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
inputs=json.loads((S/'inputs.json').read_text())
# Classification only: preserve every original snapshot and original digest.
mutable={'README.md','SCREENING.md','VALIDATION.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md','frontier/iterations/iteration39-quantum-spectral-discovery-task.json'}
for x in inputs:
 if x['path'] in mutable:x['mutable']=True
write(S/'inputs.json',inputs)
versions=[]
for p in sorted((S/'literature').glob('*-current.html')):
 text=p.read_text();name=p.name.removesuffix('-current.html');ident=re.search(r'citation_arxiv_id" content="([^"]+)',text).group(1)
 v=max(map(int,re.findall(r'\[v(\d+)\]',text)));versions.append({'name':name,'id':ident,'version':v})
write(S/'literature/versions.json',versions)
rows=json.loads((S/'selected-pinned.json').read_text());read=[]
def passage(p,ranges,scope,identity=None):
 data=p.read_bytes();lines=data.decode(errors='replace').splitlines(); spans=[]
 for a,b in ranges:
  b=min(b or len(lines),len(lines));assert 1<=a<=b
  fragment='\n'.join(lines[a-1:b]);spans.append({'first_line':a,'last_line':b,'sha256_utf8_joined_lines':sha(fragment.encode()),'labels':re.findall(r'\\label\{([^}]+)\}',fragment)})
 row={'path':str(p.relative_to(R)),'sha256':sha(data),'read_scope':scope,'ranges':spans}
 if identity:row['pinned_identity']=identity
 read.append(row)
def src(prefix,suffix,ranges,scope):
 hits=[x for x in rows if x['path'].split('/')[1].startswith(prefix) and x['path'].endswith(suffix)];assert len(hits)==1,(prefix,suffix)
 x=hits[0];passage(R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'/x['path'],ranges,scope,x)
for suffix in ['introduction.tex','model.tex','transfer.tex','bootstrap.tex','assembly.tex']:
 src('The-periodic-spin','build/'+suffix,[(1,None)],'Statement and complete relevant proof operation; read in chunks where needed.')
for suffix in ['main.tex','sections/boundary.tex','sections/conclusion.tex','sections/topology.tex']:
 src('A-boundary-field','build/'+suffix,[(1,None)],'Boundary contract/residual, conclusion or index proof; not a full audit of every companion appendix.')
for suffix,ran in [('introduction.tex',[(1,145)]),('observation.tex',[(1,None)]),('consequences.tex',[(1,None)]),('entropy.tex',[(1,None)])]:
 src('A-spectral-gap','build/sections/'+suffix,ran,'Read statement or actual observation/posterior operation, in separate bounded passages.')
src('A-two-dimensional','03-quasilocal.tex',[(1,365)],'Graph propagation/filter and exact positive quasi-local replacement proof.')
for suffix,ran in [('00-introduction.tex',[(1,None)]),('04-compression.tex',[(1,160)]),('07-assembly.tex',[(1,None)]),('08-companion-interface.tex',[(1,None)])]:
 src('Polynomial-PEPS',suffix,ran,'Early nonalgorithmic interface screen; not a full algorithm audit.')
for suffix,ran in [('01-introduction.tex',[(1,None)]),('04-warming.tex',[(1,160)]),('05-gaussian-limits.tex',[(1,145),(235,360)])]:
 src('Universality-of-critical-quench',suffix,ran,'Exact compact-time/warming contract and Gaussian subsequence passages; not a full warming proof audit.')
src('Functional-universality','09-functional.tex',[(1,165)],'Spectral representation, continuity and stationary decay.')
src('Cutoff-throughout','09-cutoff.tex',[(20,110),(365,430),(1010,1060)],'Cutoff statement, restart and final oscillation interfaces.')
lit={
 'moon-v2.pdf.txt':[(98,265),(440,610),(745,825)],
 'local-v2.pdf.txt':[(180,320),(385,425)],
 'michalakis-v3.pdf.txt':[(1,28),(140,174),(210,290),(1018,1075)],
 'tasaki-v4.pdf.txt':[(165,310)],
 'indices-v1.pdf.txt':[(265,350)],
 'ge-eisert-v2.pdf.txt':[(125,245)],
 'sk-wpi-v1.pdf.txt':[(1,150)],
 'sk-trickle-v1.pdf.txt':[(1,290)],
 'sk-overlap-v1.pdf.txt':[(129,205)],
 'wang-v2.pdf.txt':[(118,205),(875,1015)]}
for name,ran in lit.items():passage(S/'literature'/name,ran,'Primary statement and proof passages actually inspected; not a complete-paper reading claim.')
write(S/'read-passages.json',{'note':'Read log for decisive passages. Line ranges identify inspected content, not a claim that every line was semantically audited. Full inventory collection is separately recorded. Display truncations were addressed for decisive statements by subsequent bounded reads; Tasaki definitions additionally visually checked.','passages':read,'visual_checks':[{'path':str(p.relative_to(R)),'sha256':sha(p.read_bytes()),'description':d} for p,d in [(S/'literature/moon-assumptions.png','Rendered PDF page 3: local hypotheses read visually.'),(S/'literature/tasaki-endmatter.png','Rendered PDF page 7: local uniqueness/gap versus global uniqueness distinction read visually.')]]})
write(S/'contracts.json',{'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','binding_detail':'Report sections 1-6 give full equations and all quantifiers. Records below summarize the operation-level screen, not additional claims.','targets':[
 {'id':'H','hypotheses':'All even L>=2304; self-adjoint spin one; real deterministic a with max|a_j-1|<=epsilon0.','conclusion':'Exist epsilon0,delta0>0 independent of length/profile, unique ground and gap>=delta0.','sources':['HP thm:main, prop:transfer, prop:bootstrap','HB thm:main, cor:topology','area-law prop:positive'],'prior_operations':'Homogeneous spatial/physical purity squaring; boundary-specific residual; exact positive quasi-local replacement; stability under local gaps/LTQO in primary literature.','new_obligations':['Relative-error control of arbitrary disordered words through purity doubling.','Ground-aligned uniform relative-form estimate RF, or compatible local constraint kernels and the missing comparison.'],'tests':'Constant scaling; extensive Weyl cost; four-site raw-form obstruction; arbitrarily small kernel-destroying twirl.','status':'Developed gap; unproved, not refuted; no substantial nomination.'},
 {'id':'S','hypotheses':'Each fixed beta in (0,1); zero-field Gaussian SK variance beta^2/n; site-rate-one heat bath.','conclusion':'With probability tending to one, simultaneously all f, Ent_mu(f^2)<=C_beta sum_i mu Var_i(f).','sources':['SG thm:main and observation proof','SC thm:cutoff-continuous','Wang 2608.22159v2 Theorems 4.1-4.3'],'prior_operations':'Variance retention, bad-path square-tilted mass; all-field covariance to modified LSI in smaller regime; cutoff already supplied.','new_obligations':['Uniform bad-path entropy retention relative to Dirichlet energy.'],'tests':'Beta zero product case; clock scaling; rare-atom gap/LSI separation; modified versus classical LSI direction.','status':'Unclosed entropy-transfer gap; not selected.'},
 {'id':'W','hypotheses':'Critical beta=1; Gaussian and Rademacher; independent fair initial spins; T_n=n^(2/3); rate-one sites; quenched thermal expectation, n^(-2/3) sum.','conclusion':'For every 0<a<b and eta>0, lim_S limsup_n P(sup_{s>=S,a<=t<=b}|B_n-A_n|>eta)=0.','sources':['QU thm:main and thm:warming','FU 09-functional spectral-measure proof'],'prior_operations':'Compact convergence, limiting quench relaxation, Gaussian bounded kernels and weak-density subsequences, stationary spectral positivity.','new_obligations':['Uniform low-energy compactness/relaxation eliminating slow modes, including Rademacher transfer.'],'tests':'t=0 normalization singularity; actual reversible delayed-bump chain; stationary large-lag extension technical.','status':'Unclosed waiting-time gap; delayed-bump example only refutes weaker generic inference.'},
 {'id':'PEPS','hypotheses':'Family-265 rational local gapped open-square inputs; promised fixed gap and target error.','conclusion':'Polynomial input-to-tensor algorithm with polynomial bits and bond dimension.','sources':['PEPS compression, assembly, companion interface','Ge-Eisert 1411.2995v2 Theorem 8'],'prior_operations':'Existence from exact Omega private copies and product-column selection; fixed polynomial error exponent already flexible.','new_obligations':['Constructive access and stable finite-bit representation.'],'tests':'Unknown-ground-state input; no guaranteed column overlap; general area-law hardness does not refute promised local-gapped class.','status':'Early interface rejection; no complete algorithm audit or nomination.'}]})
write(S/'environment-failures.json',{'note':'Retrospective environment log; messages below are summaries, not retained verbatim stderr. Direct HTTP metadata is retained separately.','optional_imports':[{'module':'bs4','failure':'ModuleNotFoundError; replaced with standard-library regex.'},{'module':'sympy','failure':'ModuleNotFoundError; replaced with exact fractions and explicit matrices.'}],'pdf_extraction':'pdftotext emitted font warnings on some files; text retained and key local-hypothesis pages rendered/visually inspected. No extraction failure was used as a premise.','http_failures':[],'network_scope':'28 direct primary/pinned responses, plus four retained web-search tool request/response snapshots.'})
diag=runpy.run_path(str(E/'check.py'))['check']();write(E/'diagnostics.json',json.loads(json.dumps(diag,default=str)))
print(json.dumps({'inputs':len(inputs),'read_records':len(read),'versions':len(versions),'exact_checks':diag['exact_assertions']}))
