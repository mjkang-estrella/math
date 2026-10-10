"""One-shot supplementary evidence capture; not the offline verifier."""
from pathlib import Path
import hashlib,json,re,urllib.request,datetime
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i61_averaged_entropy_coefficient_rounding'
C=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def save(name,obj):
 p=S/name;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
if (S/'read-contracts.json').exists():raise SystemExit('Refuse to overwrite supplementary capture')
tree={r['path']:r for r in json.loads((S/'inputs/sources/preprints-tree.json').read_text())['tree']}
near='preprints/Near-Inclusions-of-von-Neumann-Algebras-Without-Small-Spatial-Embeddings-October-5-2026/build/sections/'
tracial='preprints/Tracial-projection-methods-and-uniform-property-Gamma-September-23-2026/build/sections/'
extra=[near+'introduction.tex',near+'obstruction.tex',tracial+'01_introduction.tex',tracial+'10_unital_averaging.tex']
pins=[]
for name in extra:
 b=(C/name).read_bytes();assert blob(b)==tree[name]['sha']
 p=S/'pinned'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 pins.append(dict(path=name,sha256=sha(b),git_blob=blob(b),url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+name))
save('additional-pins.json',pins)
copies=[]
for tag,folder,ob in [('i53','i53_sharp_entropy_stability_discovery','objections.json'),('i55','i55_sharp_entropy_stability_r2','objections.json'),('i56','i56_sharp_entropy_stability_novelty','objections-and-responses.json'),('i59','i59_dimension_uniform_entropy_stability','objections-and-responses.json')]:
 for file in ['brief.txt',ob]:
  orig=ROOT/'frontier/sources'/folder/file;b=orig.read_bytes()
  target=S/'prior-records'/tag/file;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
  copies.append(dict(original=str(orig.relative_to(ROOT)),path=str(target.relative_to(ROOT)),sha256=sha(b)))
save('prior-records.json',copies)
contracts=[];passages=[]
def read(path,ranges,purpose,status='Read these exact ranges; no claim to read the rest'):
 p=Path(path);p=p if p.is_absolute() else S/path
 lines=p.read_text().splitlines(keepends=True)
 ranges=[(a,len(lines) if b is None else b) for a,b in ranges]
 contracts.append(dict(path=str(p.relative_to(ROOT)),ranges=ranges,purpose=purpose,scope=status,sha256=sha(p.read_bytes())))
 for a,b in ranges:
  assert 1<=a<=b<=len(lines),(str(p),a,b,len(lines))
  text=''.join(lines[a-1:b]);passages.append(dict(path=str(p.relative_to(ROOT)),start=a,end=b,purpose=purpose,text=text,sha256=sha(text.encode())))
for f in ['frontier/iterations/i53-sharp-entropy-stability-discovery.md','frontier/reviews/i55-sharp-entropy-stability-r2.md','frontier/reviews/i56-sharp-entropy-stability-novelty.md','frontier/iterations/i59-dimension-uniform-entropy-stability.md']:
 read('inputs/'+f,[(1,None)],'Full mandatory predecessor read; originals unchanged','FULL')
base='pinned/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/build/manuscript/'
for f,purpose in [('introduction','exact entropy hypotheses and equality orbit'),('transport','nonlinear normalizer, covariance, transport separation'),('matrix','logdet support, chaos decomposition, scalar absorption, simultaneous surplus'),('scalar','Mills scalar bounds, absorption and pair cancellation'),('rigidity','origin jets, coefficient commutation, law reconstruction and forward q bound'),('approximation','weighted approximation of laws, not coefficient convergence'),('geometry','simplex consequence and its distinct scope')]:
 read(base+f+'.tex',[(1,None)],purpose,'FULL')
read(base+'certificate.tex',[(1,160)],'elementary derivative and scalar certificate setup; later finite certificates accepted with pinned proof operations')
mb='pinned/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/build/sections/'
read(mb+'06-linear-equality.tex',[(1,None)],'spectral two-point measure, Gaussian commutator identity and exact equality','FULL')
read(mb+'02-projections.tex',[(90,195)],'actual projection-layer operation; no identification with entropy deficit')
read(mb+'09-consequences.tex',[(1,None)],'companion consequence scope','FULL')
read('pinned/'+extra[0],[(1,None)],'operator-norm near-inclusion hypotheses','FULL')
read('pinned/'+extra[1],[(1,None)],'common-corner support/polar proof and trace-log obstruction','FULL')
read('pinned/'+extra[2],[(1,160)],'uniform Gamma and projection supply hypotheses')
read('pinned/'+extra[3],[(1,None)],'nuclear averaging, homomorphism replacement, fourth moment and clipping proof','FULL')
spec={
 'kitaev-pdf':([(1,30),(231,430)],'cb-norm hypotheses, nonpositive spectral projection, approximate C*-algebra definition and theorem; full external proof not imported'),
 'bk2026-pdf':([(1,255),(350,500)],'pair and family statements; block minimization, weighted averaging, sqrt N loss'),
 'fk-pdf':([(70,205)],'Theorems 2 and 3, block proof and iteration'),
 'bdhr-pdf':([(320,415)],'exact positive-inner-product associative decomposition'),
 'bds-journal':([(420,510)],'published Proposition 4.1 tangent; complex examples scope'),
 'robeva-pdf':([(965,1040)],'Lemma 3.7 Jacobian proof'),
 'auddy-pdf':([(640,665),(870,940),(2199,2260)],'existing odeco comparison, isometry hypothesis (25), polar-factor construction'),
 'cpv-pdf':([(250,460)],'exact C*-representation and Frobenius orthogonal-basis classification'),
 'hilbert-frobenius':([(155,180),(1187,1228)],'exact Hilbertian algebra and approximate units, not approximate associativity'),
 'fms-pdf':([(585,610),(680,750)],'entropy/isotropic statement and cone-lift integral calculation'),
 'mnr-pdf':([(75,92),(314,360)],'scalar theorem and rearrangement variance operation')}
for f,(ranges,purpose) in spec.items():read('literature/'+f+'.txt',ranges,purpose)
save('read-contracts.json',contracts);save('passages.json',passages)
versions=[]
for p in sorted((S/'literature').glob('*-pdf.txt')):
 hit=re.search(r'arXiv:[0-9.]+v\d+[^\n]*',p.read_text())
 assert hit,p
 versions.append(dict(path=str(p.relative_to(ROOT)),served_version=hit.group(0),note='Version read from freshly served PDF; current abs and PDF responses retained separately'))
save('literature/versions.json',versions)
responses=[]
allpins=json.loads((S/'pins.json').read_text())+pins
selected=[r for r in allpins if r['path'].endswith('/rigidity.tex') or r['path'].endswith('/scalar.tex') or r['path'].endswith('/obstruction.tex') or r['path'].endswith('/10_unital_averaging.tex')]
for j,row in enumerate(selected):
 rec=dict(name='pinned-'+str(j),url=row['url'],retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(row['url'],headers={'User-Agent':'I61 primary-source audit'}),timeout=30) as response:
   b=response.read();rec.update(status=response.status,final_url=response.url,headers=dict(response.headers))
  p=S/'primary-pinned'/('response-'+str(j)+'.tex');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
  rec.update(path=str(p.relative_to(ROOT)),sha256=sha(b),bytes=len(b),expected_git_blob=row['git_blob'],actual_git_blob=blob(b),matches_pin=blob(b)==row['git_blob'])
 except Exception as exc:rec.update(status='FAILED',error=repr(exc))
 responses.append(rec)
save('primary-pinned/manifest.json',responses)
save('search-notes.json',dict(scope='Bounded primary-literature search and complete pinned-corpus line-multiset audit. Absence of exact duplicate is not a priority or substantiality proof.',primary_queries=['approximate Frobenius algebra stability orthogonal tensor normalized Hilbert Schmidt','Kitaev almost idempotent quantum channel approximate C star algebra','Bansil Kachkovskiy almost commuting self adjoint matrices 2026','orthogonally decomposable tensor perturbation Auddy Yuan Robeva'],selected_hits=['Kitaev','Coecke-Pavlovic-Vicary','Poinsot','Bansil-Kachkovskiy','Filonov-Kachkovskiy','BDS','BDHR','Robeva','Auddy-Yuan'],companion_scope='Entropy and general Mahler proof operations; near-inclusion and tracial Gamma operator-algebra companions. No I60 threshold/combinatorial lane investigation.',mathdb='No verified problem score; none claimed.',retrieval='23 successful literature responses; 13 extracted PDFs. Supplementary raw pinned responses have their own status/error records. Historical failures preserved in prior-hashes, not silently changed.'))
print(json.dumps(dict(contracts=len(contracts),passages=len(passages),supplementary_pins=len(pins),prior_record_copies=len(copies),raw_responses=[r['status'] for r in responses])))
