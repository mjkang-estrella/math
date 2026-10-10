"""Discovery-time manifest builder. NOT the final verifier; never seals/reseals."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i113_online_optimization_discovery'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(name,x):(S/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
refs=[]
for rel in ['frontier/sources/i88_nonlinear_banach_discovery/search-domain.json',
            'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json',
            'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl',
            'frontier/sources/i22_combinatorial_discovery/literature/manifest.json']:
    refs.append({'path':rel,'sha256':sha(ROOT/rel),'bytes':(ROOT/rel).stat().st_size})
primary=json.loads((ROOT/'frontier/sources/i22_combinatorial_discovery/literature/manifest.json').read_text())
for d in primary:
    if d['name'] in ['iff-sfm','strong-secretary','sample-ocrs','sample-prophet']:
        assert sha(ROOT/d['path'])==d['sha256']
        refs.append(d)
put('immutable-references.json',refs)
external=[json.loads(p.read_text()) for p in sorted((S/'external').glob('*.response.json'))]
put('external-manifest.json',external)
reads=[]
def passage(rel,start,end,convention,purpose,url=None):
    raw=(ROOT/rel).read_bytes(); text=raw.decode('utf-8',errors='replace')
    lines=text.splitlines() if convention=='splitlines' else text.split('\n')
    if end is None:end=len(lines)
    assert 1<=start<=end<=len(lines),(rel,start,end,len(lines))
    item={'path':rel,'sha256':sha(ROOT/rel),'line_convention':convention,
          'start':start,'end':end,'total_lines':len(lines),
          'passage_encoding':'UTF-8 errors=replace; selected lines joined by LF; no appended LF',
          'passage_sha256':hashlib.sha256('\n'.join(lines[start-1:end]).encode()).hexdigest(),
          'purpose':purpose}
    if url:item['url']=url
    reads.append(item)
selected=json.loads((S/'selected-inventory.json').read_text())
for d in selected:
    q=d['path']; name=Path(q).name
    if '/sections/' not in q:continue
    full=(any(x in q for x in ['One-Sample-Suffices','Turn-Based-Stochastic','Uniform-computation'])
          or ('Mean-payoff-parity-games' in q and name!='history.tex')
          or ('Deterministic-quasipolynomial' in q and name=='07-values-and-strategies.tex'))
    if full:passage(d['local'],1,None,'splitlines','Complete accepted theorem/proof operation; see report source abbreviations',d['url'])
base='frontier/sources/i22_combinatorial_discovery/literature/'
for name,start,end,purpose in [
 ('strong-secretary',1,100,'Theorem statements and scope'),
 ('strong-secretary',730,916,'Complete section 5 algorithm, invariant and guarantee through proof ending'),
 ('sample-ocrs',90,270,'Almighty OCRS and chain interface, including Theorem 2.5 ending'),
 ('sample-prophet',1309,None,'Appendix C lower-bound comparison through ending; imported lemma distinguished'),
 ('iff-sfm',278,612,'Scaling algorithm correctness/complexity and strongly polynomial modification through theorem and pseudocode ending')]:
    original=next(d for d in primary if d['name']==name and d['path'].endswith('.pdf'))
    passage(base+name+'.txt',start,end,'LF',purpose,original['url'])
for name,ranges in {
 'dk19':[(1,210,'Known-prior inaccurate-input scope'),(1120,1303,'Theorems 5.1 and 6.1 full proof comparison and ending examples')],
 'stochastic-parity':[(195,263,'Exact limsup-average and largest-priority objective definitions'),(427,684,'Lemma 2 full increasing-phase proof, Lemma 3 interface and algorithm through conclusion')],
 'cc26':[(328,755,'Implementation scope and propositions 4-7; proof of 5,7 and proof sketch of 6 through end; Lemma 9 expressly imports external details')]
}.items():
    url=next(d['url'] for d in external if d['path'].endswith('/'+name+'.pdf'))
    for start,end,purpose in ranges:passage(str((S/'external'/f'{name}.txt').relative_to(ROOT)),start,end,'LF',purpose,url)
put('read-manifest.json',{'note':'Declared actual readings; this is not a claim of semantic coverage of all lexical matches. Corpus uses splitlines; PDF text uses LF, preserving form-feed characters. No replay extraction.', 'passages':reads})
print(json.dumps({'immutable_reference_records':len(refs),'external_originals':len(external),'reading_passages':len(reads)}))
