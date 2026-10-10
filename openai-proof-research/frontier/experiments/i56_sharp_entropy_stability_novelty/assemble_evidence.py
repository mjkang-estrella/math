"""One-time evidence assembly; not called by the read-only verifier."""
from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i56_sharp_entropy_stability_novelty'
A=ROOT/'frontier/sources/i53_sharp_entropy_stability_discovery'
C=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
sha=lambda b:hashlib.sha256(b).hexdigest()
def dump(name,obj):
 p=S/name
 if p.exists():raise RuntimeError('Refusing overwrite: '+str(p))
 p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
rows=[]
for x in json.loads((A/'pinned-manifest.json').read_text()):
 p=A/'pinned'/x['path']; b=p.read_bytes(); dest=S/'pinned'/x['path'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 rows.append({**x,'local':str(dest.relative_to(ROOT))})
extras=['preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/build/sections/introduction.tex','preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/introduction.tex','preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/build/main.tex']
for p in extras:
 b=(C/p).read_bytes();dest=S/'pinned'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 rows.append({'path':p,'local':str(dest.relative_to(ROOT)),'sha256':sha(b),'git_blob':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),'url':'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+p})
dump('pinned-manifest.json',rows)
passages=[]
def add(path,first,last,purpose):
 lines=(ROOT/path).read_text().splitlines(keepends=True);last=min(last,len(lines)); excerpt=''.join(lines[first-1:last]);passages.append({'path':path,'first_line':first,'last_line':last,'purpose':purpose,'sha256':sha(excerpt.encode()),'passage':excerpt})
for x in rows:
 n=Path(x['path']).name
 if 'A-sharp-entropy' in x['path']:
  add(x['local'],1,len((ROOT/x['local']).read_text().splitlines()),'Complete main-family file; proof operations treated as premises, not upstream truth audit.')
 elif n=='06-linear-equality.tex':add(x['local'],300,490,'General Mahler strictness, equality, commutation and cone product; different defect.')
 elif n=='09-consequences.tex':add(x['local'],1,90,'Functional limiting passage does not transfer equality; different entropy-transport assumptions.')
 elif n=='02-projections.tex':add(x['local'],1,170,'Different projection normalization and layer field.')
 else:add(x['local'],1,110,'Companion statement and relevance screen.')
L='frontier/sources/i56_sharp_entropy_stability_novelty/literature/'
for name,ranges in {
 'odeco-pdf':[(355,412,'Exact associativity and converse proof')],
 'biaggi-journal':[(408,455,'Published tangent-space proof and smoothness remark')],
 'biaggi-pdf':[(345,379,'Preprint tangent-space proof; numbering differs')],
 'robeva-pdf':[(965,1040,'Earlier Jacobian-rank proof credited by Biaggi et al.')],
 'auddy-yuan-pdf':[(640,662,'Two already odeco tensors'),(866,932,'Nearly isometric factors are the input'),(1154,1205,'Perturbation proof setup'),(2199,2295,'Polar factor construction proof')],
 'sroa-pdf':[(373,435,'Known odeco plus additive perturbation; variational bounds'),(458,535,'First-order proof'),(672,775,'Controlled deflation and its proximity input')],
 'fk-pdf':[(1,233,'Full spectral partition proof and matrix-count exponent')],
 'fms-pdf':[(315,342,'Strong entropy/isotropic conjecture'),(580,744,'Cone formulas and auxiliary dimensions'),(780,863,'Proof of strong slicing implications')],
 'mnr-author':[(65,108,'Scalar entropy theorem'),(260,398,'Rearrangement proof'),(420,575,'Degrees of freedom and localization'),(578,611,'Scalar final proof setup')],
 'rademacher-pdf':[(78,104,'Local symmetry and simplicial maximizer statements'),(505,598,'Facet variation calculations and simplex proof')],
 'kipp-pdf':[(180,210,'Decomposability bound'),(1257,1305,'Kernel and second-variation proof')],
 'kipp-platonic-pdf':[(89,121,'Simplicial vertex theorem and mechanism')],
 'simplex-pdf':[(68,150,'Stability of direction in a fixed simplex'),(390,463,'Near-direction proof mechanism')]
}.items():
 for a,b,why in ranges:add(L+name+'.txt',a,b,why)
dump('passages.json',passages)
versions=[]
for mf in ['manifest.json','manifest-additional.json']:
 for x in json.loads((S/'literature'/mf).read_text()):
  if x.get('extraction'):
   p=ROOT/x['extraction']['path'];txt=p.read_text(); mat=re.search(r'arXiv:\s*([\d.]+v\d+)',txt)
   versions.append({'name':x['name'],'path':str(p.relative_to(ROOT)),'pdf_response_filename':x.get('headers',{}).get('content-disposition'),'version_in_text':mat.group(1) if mat else None,'first_page_text':txt.split('\f')[0][:1600]})
dump('literature-versions.json',versions)
objections=[
 ('O1','Equation residual is different from assumed proximity.','I53 §§4,7 correctly separates its input from Auddy–Yuan and Mu–Hsu–Goldfarb.','SUSTAIN distinction; OVERRULE significance inference. Review §2 supplies proximity and linear residual control.','Closed for H53; no algorithmic threshold claimed.'),
 ('O2','Compactness alone supplies no power and may hide singular strata.','I53 avoids compactness and treats generic Lojasiewicz as insufficient novelty.','Review (2.3)–(2.10) proves the entire real normalized kernel, exact normal coercivity, quadratic remainder and compact entrance.','Closed, without Lojasiewicz.'),
 ('O3','Explicit threshold and quadratic deflation may distinguish Lemma A.','I53 η≤10^-6 m^-4 and distance≤20mη, with quadratic restriction growth.','Useful constructive lemma, dispensable for identical H53 scope and exponent; final C_m has no optimized size.','TECHNICAL ONLY at nominated theorem.'),
 ('O4','Weak compatibility could be a nonroutine analytic barrier.','I53 §3 distributional mollification avoids differentiating an arbitrary L2 error.','Source exact two jets + bounded finite-parameter family + bump scaling prove the same exponent; review §3 pays all constants by dimension-only bounds.','Closed for fixed m; uniform U still unpaid.'),
 ('O5','Affine normalization or nonsmooth support could defeat the alternative.','I53 §6 uses source Jensen, first chaos, coupling and weighted approximation.','Independent covariance inequality gives P≥I/2 for small r; source approximation then proves full scope.','Closed.'),
 ('O6','Simplex or dimension-uniform potential may support significance.','I53 §9 explicitly leaves both open.','Neither contributes to H53 classification.','Both remain unpaid; no count recommendation for consequences.'),
 ('O7','Lack of an exact prior theorem might support novelty.','I53 bounded primary search finds no exact statement and disclaims worldwide priority.','No exact duplicate certified; explicit routine reduction establishes TECHNICAL ONLY.','No worldwide priority or MathDB score.'),
 ('O8','Original evidence contains a failed inventory verification.','I53 preserves first seal and FAIL and corrects path-order comparison only.','Unchanged original corrected verifier independently PASS; old failure and seals frozen.','Evidence history preserved; no mathematical repair inferred.')]
dump('objections-and-responses.json',[dict(zip(['id','objection','recorded_author_position','review_response','disposition'],r)) for r in objections])
dump('reading-scope.json',{'main_family':'Complete 11 cached source files; statements and proof operations, including full equality/compactness.','companion_scope':'General Mahler selected proof sections, symmetric Mahler and logBM introductions, projection-body comparison statement.','inventory':'All 749 roots and all 9340 files inventoried; targeted whole-corpus text search, not a claim every file was read.','primary_passages':len(passages),'new_primary_antecedent':'Biaggi–Draisma–Seynnaeve published Proposition 4.1; earlier Robeva Lemma 3.7.','visual_qa':[{'name':'biaggi-journal','page':10},{'name':'odeco-pdf','page':8},{'name':'fk-pdf','page':4}],'upstream_truth':'Accepted, not independently audited.'})
print('pins',len(rows),'passages',len(passages),'versions',len(versions))
