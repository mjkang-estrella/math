"""One-shot I64 reading and dependency evidence assembly, within assigned paths only."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i64_entropy_coefficient_extraction_novelty';C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def put(p,x):
 with p.open('x') as f:json.dump(x,f,indent=2);f.write('\n')
# Freeze the completed dependency only after the user's explicit in-flight update.
a=[]
for p in ['frontier/reviews/i63-entropy-coefficient-extraction-r2.md','frontier/experiments/i63_entropy_coefficient_extraction_r2/verify.py','frontier/sources/i63_entropy_coefficient_extraction_r2/seal.json']:
 b=(R/p).read_bytes();dest=S/'inputs'/p;dest.parent.mkdir(parents=True,exist_ok=True)
 with dest.open('xb') as f:f.write(b)
 a.append(dict(path=p,sha256=sha(b),mutable=False))
put(S/'inflight-inputs.json',a)
contracts=[];passages=[]
def contract(p,ranges,role,kind='proof operation'):
 b=p.read_bytes();lines=b.decode().splitlines(keepends=True)
 if ranges=='full':ranges=[(1,len(lines))]
 row=dict(path=str(p.relative_to(R)),sha256=sha(b),ranges=ranges,role=role,kind=kind)
 contracts.append(row)
 for start,end in ranges:
  assert 1<=start<=end<=len(lines),(p,start,end,len(lines))
  text=''.join(lines[start-1:end]);passages.append(dict(path=row['path'],start=start,end=end,text=text,sha256=sha(text.encode())))
for p in ['frontier/iterations/i61-averaged-entropy-coefficient-rounding.md','frontier/iterations/i59-dimension-uniform-entropy-stability.md','frontier/iterations/i53-sharp-entropy-stability-discovery.md','frontier/reviews/i55-sharp-entropy-stability-r2.md','frontier/reviews/i56-sharp-entropy-stability-novelty.md','frontier/experiments/i61_averaged_entropy_coefficient_rounding/verify.py','frontier/reviews/i63-entropy-coefficient-extraction-r2.md','frontier/experiments/i63_entropy_coefficient_extraction_r2/verify.py']:
 contract(S/'inputs'/p,'full','Full original text; I63 read only after independent contribution draft','full report/verifier read')
for row in json.loads((S/'pins.json').read_text()):
 p=S/'pinned'/row['path']
 if p.name not in ['README.md','main.tex','references.bib']:
  contract(p,'full','Full actual selected source proof/companion; statements and lower operations stipulated','full selected source read')
# Additional companion screening passages, not a claim to have read each complete manuscript.
extra=[('Universal-strong-Kadison*/build/sections/02*',[(180,260)],'cb multiplication correction assumes an existing associative algebra'),('Universal-strong-Kadison*/build/sections/03*',[(775,906)],'spectral clipping preserves columns and weighted supports'),('Universal-strong-Kadison*/build/sections/05*',[(200,275)],'random sign fourth moment and L2 clipping'),('Universal-strong-Kadison*/build/sections/06*',[(330,460)],'weighted graph signal retained by fourth moment clipping'),('Tracial-projection*/build/sections/14*',[(1,45)],'nonunital aggregate model statement and its hypotheses'),('Uniform-Bi-Holder*/build/sections/spectral.tex',[(1,40)],'fixed-manifold Jacobi comparison; screening exclusion'),('Vanishing-of-higher-bounded-Hochschild*/build/sections/05*',[(1,85)],'fixed algebra bounded-ball continuity; screening exclusion')]
extras=[]
for pat,ranges,role in extra:
 p=next((C/'preprints').glob(pat));rel=p.relative_to(C);b=p.read_bytes();dest=S/'pinned'/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 with dest.open('xb') as f:f.write(b)
 extras.append(dict(path=str(rel),sha256=sha(b),git_blob=blob(b),url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+str(rel)))
 contract(dest,ranges,role)
put(S/'additional-pins.json',extras)
D=S/'literature'
reads=[('fk-pdf','full','Whole count-dependent block proof'),('bk2026-pdf','full','Whole pair/family spectral-partition proof and count loss'),('bds-journal',[(410,493)],'Proposition 4.1 tangent equations and proof'),('robeva-pdf',[(968,1055)],'Lemma 3.7 Jacobian/tangent proof'),('bdhr-pdf',[(330,419)],'Lemmas 10/11 and Proposition 12 exact real associativity'),('auddy-pdf',[(640,714),(895,1000),(2238,2390)],'Theorems 2.4/3.1 and supplied-factor polar proof'),('kitaev-pdf',[(194,390)],'Channel hypotheses, non-CP projection warning, Banach axioms and theorem'),('cpv-pdf',[(385,480)],'Exact orthogonal-basis correspondence and special normalization'),('hilbert-frobenius',[(1180,1255)],'Exact algebra and approximate-unit distinction'),('tropp-analysis',[(6595,6700)],'Daleckii-Krein statement, not antisymmetrized coercivity'),('tropp-moments',[(80,153),(860,910)],'Matrix variance, Khintchine, logarithmic norm loss, Gaussian IBP'),('hosvd',[(815,881),(935,984)],'Property 10 and actual core-energy proof'),('yang-hodge',[(76,130),(270,315)],'Gaussian Hodge theorem and dimension-independent chaos formulation'),('korn',[(1,128)],'Incompatible-field theorem and its domain constants'),('fms-pdf',[(585,615),(680,749)],'Proposition 5.2 and cone moment calculation'),('mnr-journal',[(75,98),(319,350),(433,466),(500,535)],'Scalar entropy, rearrangement, extreme-point reduction')]
for name,ranges,role in reads:contract(D/(name+'.txt'),ranges,role,'external primary applicability/proof passage')
put(S/'read-contracts.json',contracts);put(S/'passages.json',passages)
primary=json.loads((D/'manifest.json').read_text())+json.loads((D/'supplement.json').read_text());versions=[];raw=[]
pins=json.loads((S/'pins.json').read_text())
for row in primary:
 if row.get('text_path'):
  text=(R/row['text_path']).read_text();v=re.findall(r'arXiv:\s*([\d.]+v\d+)',text)
  versions.append(dict(name=row['name'],url=row['url'],arxiv_pdf_header_versions=sorted(set(v)),first_page_header=text[:1300],text_sha256=sha(text.encode())))
 if row['name'].startswith('raw-'):
  matches=[p for p in pins if p['url']==row['url']];assert len(matches)==1;p=matches[0]
  assert (R/row['path']).read_bytes()==(S/'pinned'/p['path']).read_bytes()
  raw.append(dict(response=row['path'],pin=str((S/'pinned'/p['path']).relative_to(R)),git_blob=p['git_blob']))
put(D/'versions.json',versions);put(S/'raw-pin-comparisons.json',raw)
print(json.dumps(dict(initial_inputs=15,inflight_inputs=3,contracts=len(contracts),passages=len(passages),pins=19+len(extras),requests=len(primary),successes=sum(r.get('status')==200 for r in primary),pdfs=len(versions))))
