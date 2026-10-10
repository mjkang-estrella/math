from pathlib import Path
import json,re,hashlib,subprocess,urllib.request,datetime
S=Path('frontier/sources/i82_measured_group_operator_discovery')
def sha(b):return hashlib.sha256(b).hexdigest()
domain=json.load(open('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json'))
patterns={
'families':r'fixed.price|strong.{0,8}Ulam|unitarizab|equivariant.{0,30}(Gamma|Jiang)|near.inclusion|spatial.conjug|Kadison.Kastler',
'quantitative':r'empirical.covariance|Lindeberg|square.root.normal|regulariz.{0,50}covariance|polynomial.{0,40}row|row.{0,40}polynomial',
'cost_iso':r'ergodic.{0,40}cost|cost.{0,40}ergodic|abstract.{0,30}(isomorph|automorph)|normaliz.{0,40}tensor.norm'}
search=[]
for name,pat in patterns.items():
 rx=re.compile(pat,re.I);hits=[]
 for x in domain:
  p=Path(x['local']); b=p.read_bytes()
  for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
   if rx.search(line):hits.append({'path':x['path'],'local':str(p),'line':i,'text':line})
 out=S/('search-'+name+'.json');out.write_text(json.dumps(hits,indent=2)+'\n')
 search.append(dict(name=name,pattern=pat,flags='IGNORECASE',lines=len(hits),output=str(out),sha256=sha(out.read_bytes())))
(S/'searches.json').write_text(json.dumps(search,indent=2)+'\n')
refs=[]
for p in ['sources/preprints-tree.json','sources/upstream.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/seal-v1.json']:
 refs.append(dict(path=p,sha256=sha(Path(p).read_bytes())))
(S/'immutable-references.json').write_text(json.dumps(refs,indent=2)+'\n')
print('domain',len(domain),'kinds', {k:sum(x['kind']==k for x in domain) for k in set(x['kind'] for x in domain)},'searches',[(x['name'],x['lines']) for x in search])
