"""Acquisition-time metadata construction. Never called by read-only replay."""
import json,re,hashlib
from pathlib import Path
S=Path('frontier/sources/i129_disordered_fk_occupation')
assert not (S/'seal.json').exists(), 'Cannot modify a sealed package'
def load(p):return json.loads(Path(p).read_text())
def save(p,v):Path(p).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def row(p):
    b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
roots=sorted([
 'Natural-Occupation-Measures-for-Critical-Square-Lattice-FK-Interfaces-October-5-2026',
 'Quenched-SLE-Universality-for-Weakly-Disordered-FK-Ising-Interfaces-October-5-2026',
 'Quenched-SLE3-Universality-for-the-Weak-Random-Bond-Ising-Model-October-5-2026'])
save(S/'family-roots.json',roots)
domain=load('frontier/sources/i114_quantum_information_discovery/search-domain.json')
selected=[r for r in domain if r['path'].split('/')[1] in roots]
save(S/'selected-inventory.json',selected)
lookup={r['local']:r for r in domain}
reads=load(S/'read-manifest.json')
for r in reads:
    if r['local'] in lookup:
        r['domain_path']=lookup[r['local']]['path']
        r['url']='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+r['domain_path']
save(S/'read-manifest.json',reads)
files=sorted({r['local'] for r in selected if r['local'].endswith(('.tex','.md'))}|{str(p) for p in (S/'external').glob('*.txt')})
pattern=r'two.arm|strand|normaliz\w*|partition|variance|charge|anneal\w*|quenched|summab\w*|boundary|occupation|calibr\w*|posterior|scalar|critical'
save(S/'lexical-query.json',dict(pattern=pattern,flags='IGNORECASE',files=files,convention='UTF-8 splitlines, one-based line and zero-based Python character offsets; all occurrences retained'))
rg=re.compile(pattern,re.I);out=[]
for p in files:
    for n,line in enumerate(Path(p).read_text().splitlines(),1):
        for m in rg.finditer(line):out.append(dict(path=p,line=n,start=m.start(),end=m.end(),text=m.group(),line_text=line))
save(S/'lexical-results.json',out)
views=[]
for p in sorted((S/'external').glob('*.html')):
    q=p.with_suffix('.txt');views.append(dict(html=str(p),html_sha256=row(p)['sha256'],text=str(q),text_sha256=row(q)['sha256']))
save(S/'html-views.json',views)
deps=[
 'frontier/experiments/i114_quantum_information_discovery/html_text.py',
 'frontier/experiments/i123_thermal_production_stability/verify.py',
 'frontier/experiments/i126_random_geometry_discovery/verify.py',
 'frontier/experiments/i126_random_geometry_discovery/check.py',
 'frontier/sources/i123_thermal_production_stability/seal.json',
 'frontier/sources/i126_random_geometry_discovery/seal.json',
 'frontier/sources/i114_quantum_information_discovery/search-domain.json']
save(S/'engine-dependencies.json',[row(p) for p in sorted(deps)])
failures=[
 dict(operation='Initial broad ledger search',issue='Terminal output truncated',disposition='All ledger bytes frozen; only relevant passages and later explicit read ranges count as semantic reading.'),
 dict(operation='Initial rg source discovery',issue='Ignored corpus did not appear in default rg --files',disposition='Used the inherited corpus mapping and explicit paths; no absence inference.'),
 dict(operation='Combined decoded I126 261-750 and I123 1-230 readings',issue='Aggregate tool output truncated',disposition='Recovered I126 360-750, later 261-359, and I123 1-230 in bounded calls; complete decoded field coverage retained.'),
 dict(operation='Pure occupation 06-coupling 1-558',issue='Output truncation near the ending',disposition='Recovered 430-558 explicitly; retained both read records.'),
 dict(operation='Disordered FK boundary 1-527',issue='Output truncation at beginning',disposition='Recovered 1-80 explicitly.'),
 dict(operation='First web search and combined second search/I126 read',issue='Displayed web/search aggregate truncated',disposition='Full returned search objects saved; primary papers acquired directly. I126 1-80 recovered; original report also supplied in full task/user context.'),
 dict(operation='Long-line external search via rg',issue='Terminal output truncated',disposition='Search is only a lead; bounded full source ranges subsequently read. No semantic completeness inferred from search.'),
 dict(operation='Raw I126 parent receipt 1-190',issue='Very long serialized stdout caused display truncation',disposition='Full receipt frozen; decoded parent_review read separately; complete result and stdout were supplied in the original user brief. No full raw-line semantic read claim.'),
 dict(operation='Combined current ledger ending ranges',issue='Output truncated inside frontier/README ending',disposition='Partial ledger read only; latest I126/I129 section of iterations/README and relevant TEN-FINDINGS entries displayed fully.'),
 dict(operation='New primary-source HTTP acquisition',issue=None,disposition='All six requests succeeded; no new PDF extraction. All older failed/truncated retrievals remain in immutable inherited evidence.')]
save(S/'failure-log.json',failures)
print(json.dumps(dict(selected_positions=len(selected),lexical_occurrences=len(out),read_records=len(reads),html_views=len(views))))
