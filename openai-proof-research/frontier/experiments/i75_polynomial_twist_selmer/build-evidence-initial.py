"""Author-time binder only. Do not run to verify or refresh a seal."""
import pathlib,json,hashlib,datetime,urllib.request
R=pathlib.Path('.');S=R/'frontier/sources/i75_polynomial_twist_selmer';E=R/'frontier/experiments/i75_polynomial_twist_selmer';old=R/'frontier/sources/i73_arithmetic_geometry_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
records=[]
def bind(path,ranges,operation):
 p=R/path;lines=p.read_bytes().splitlines(keepends=True)
 for lo,hi in ranges:
  assert 1<=lo<=hi<=len(lines),(path,lo,hi,len(lines))
  records.append({'path':str(p),'lines':[lo,hi],'sha256':sha(b''.join(lines[lo-1:hi])),'operation':operation})
g=old/'pinned/preprints/Goldfelds-analytic-density-conjecture-and-the-2-converse-for-elliptic-curves-October-7-2026/build/sections'
for name,ranges,op in [
 ('01-preliminaries.tex',[(12,76),(174,200)],'Full Kummer sequence, parity, isogeny/base-change coranks, finite descent correction'),
 ('09-local-matrices.tex',[(70,112),(140,197)],'Reciprocity symmetry and finite prime-template realization; not polynomial product counting'),
 ('07-prime-graphs.tex',[(560,584)],'Address lemma consumes realization freedoms and contraction rules'),
 ('08-rational-converse.tex',[(810,851)],'Full two-torsion packets, oriented lifts and reserve requirements'),
 ('11-conclusions.tex',[(1,85)],'Pointwise converse and separate all-integer density input')]:bind(g/name,ranges,op)
pf=old/'pinned/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/build/sections'
bind(pf/'02-sieve.tex',[(1,154)],'Fixed cutoff, large-square tail and fixed congruences')
# Bind the actual separable-products statement by its label location.
p=pf/'01-introduction.tex';ls=p.read_text().splitlines();i=next(i for i,l in enumerate(ls) if 'cor:separable-products' in l);bind(p,[(max(1,i-2),min(len(ls),i+48))],'Separable-product squarefree corollary applied to explicit quadratic/quartic')
mean=old/'pinned/preprints/The-mean-analytic-rank-of-quadratic-twists-of-elliptic-curves-October-6-2026/build/sections'
bind(mean/'tail.tex',[(1,85),(109,220)],'Counting range, Jensen and final weighted tail; inherited audited budget')
bind(mean/'analytic.tex',[(784,855)],'Source comparison length and coefficient budgets; inherited audited budget')
bind(old/'primary/ks-v1.txt',[(150,204),(462,590),(1265,1319),(2470,2590),(4052,4105)],'Fixed module, quasi-local conditions, weighted grids, reciprocity expansion, finite isogeny minimum')
bind(old/'primary/smith-v1.txt',[(101,221),(365,563)],'Balanced classification, finite-level convention, full Kummer higher pairings and controllability')
for name,ranges,op in [
 ('kps.txt',[(240,367),(1679,1783)],'Actual local planes, principal minor/cofactor cost, and proof bounds full Selmer moments'),
 ('smith-I.txt',[(1472,1534),(1900,1954),(2088,2140)],'Readiness, character estimate and weighted Fourier inversion'),
 ('smith-II.txt',[(1950,2032)],'Prime-type balance and discarded full-ideal measure'),
 ('field-change.txt',[(538,589),(590,684)],'Local Shapiro, decorated Weil restriction, adjointness and degree factor'),
 ('zhang.txt',[(245,341),(978,997)],'Actual covers, Monsky coordinates, tangent pairing, finite-level kernel'),
 ('dokchitser.txt',[(971,995)],'Scalar quadratic inertia action and discriminant twisting')]:bind(S/'primary'/name,ranges,op)
(S/'passages.json').write_text(json.dumps(records,indent=2)+'\n')
render=[]
for page in [2,3,4,6,7,8,9,10]:
 p=S/'primary'/f'tunnell-page-{page:02}.png';render.append({'pdf':str(S/'primary/tunnell.pdf'),'page':page,'dpi':100,'path':str(p),'sha256':sha(p.read_bytes()),'printed_page':page+321})
(S/'render-bindings.json').write_text(json.dumps(render,indent=2)+'\n')
(S/'tunnell-reading.json').write_text(json.dumps({'source':'primary/tunnell.pdf','method':'Visual reading of complete retained pages; pdftotext emits only the cover catalogue. No OCR inferred theorem text.','relevant_operations':{'325':'Ternary representation identity and CM curve/newform level 32.','327':'Hecke character descriptions; signed quadratic theta series with sign on the 8*z^2 variable.','328':'Coefficient identity and Theorem 3: L(E^d,1)=a(d)^2 beta/(4 sqrt(d)) for odd squarefree positive d.','329':'Positive real period beta and proof comparing Waldspurger coefficient spaces and base L-values.','330':'BSD converse and precise Sha claims are presented as conjectures here; they are not used as unconditional external theorems.'},'finite_certification':'Independent exact enumeration and signed theta convolution agree. This does not prove a density law.'},indent=2)+'\n')
(S/'capture-notes.json').write_text(json.dumps({'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat(),'complete_message':'Recovered in five 10000-character-max chunks from the current thread user message; no trailing newline in original. Parent brief contains one trailing newline.','thread_id':'thread:delegated-task:command%3Amcp%3A7d16aa64-3b21-41e0-aa56-20668921fdc9%3Adelegate-task%3Amathdb-i75-polynomial-twist-selmer-20261009','local_failures':['Initial broad file listing and concatenated ledgers caused truncated terminal output; not treated as full inventories or complete readings.','A guessed squarefree source sections/03-general.tex path was absent; corrected with rg --files --no-ignore.','An oversized maxCharsPerItem=100000 thread request returned non-JSON error text; parsing failed with Unexpected token o in tool call e...; recovered using bounded 10000-character chunks. The raw rejected response was not retained.','The initial independent theta sign transcription failed an exact assertion; complete initial code and failure description are retained.'],'discovery':'Web searches located primary author/arXiv PDFs and Tunnell original scan. Secondary snippets (including rank lists and surveys) are not proof inputs.','network':'All retained urllib source requests succeeded. No failed network retrieval is hidden.','scope':'No repeated corpus catalogue screen; inherited fixed-domain inventory and comparisons replayed by unchanged I73 verifier.','read_limits':'Retention is not a claim that every line of every retained PDF or companion was read.'},indent=2)+'\n')
# One fresh immutable raw replay of the local realization operation.
j=json.loads((old/'pinned.json').read_text());pname='preprints/Goldfelds-analytic-density-conjecture-and-the-2-converse-for-elliptic-curves-October-7-2026/build/sections/09-local-matrices.tex';rec=next(x for x in j if x['path']==pname)
url=rec['raw_url'];out=S/'primary/pin-local-matrices.tex';r={'url':url,'path':str(out),'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pin_path':str(old/'pinned'/pname),'git_blob':rec['blob']}
try:
 with urllib.request.urlopen(url,timeout=45) as f:b=f.read();r.update(status=f.status,headers=dict(f.headers.items()),final_url=f.url)
 out.write_bytes(b);r.update(sha256=sha(b),bytes=len(b));assert b==(old/'pinned'/pname).read_bytes();r['pin_comparison']='identical'
except Exception as ex:r['error']=repr(ex)
(S/'request-pin.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'passages':len(records),'scan_pages':len(render),'raw_pin_status':r.get('status'),'raw_pin_comparison':r.get('pin_comparison')},indent=2))
