from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures,re,datetime
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r93'; PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
t=json.loads((ROOT/'sources/preprints-tree.json').read_text());assert len(t['tree'])==13223 and t['truncated'] is False
select={'Blochs-Conjecture': ['introduction.tex','reductions.tex','conclusion.tex','derived.tex'], 'The-equivariant-cohomological-Hikita':['introduction.tex','deformations.tex','correspondences.tex','counting.tex','cocharacters.tex'], 'A-high-arity-counterexample':['01-introduction.tex','03-detector.tex','08-support.tex'], 'Contact-Fano-manifolds':['introduction.tex','homogeneous.tex','descent.tex'], 'A-Complete-Local-Domain':['paper.tex','surface.tex','references.bib'], 'Rational-homology-and-Quillens':['01-introduction.tex','02-reductions.tex','03-propagation.tex','10-conclusion.tex']}
es=[e for e in t['tree'] if e['type']=='blob' and any(e['path'].split('/')[1].startswith(k) and Path(e['path']).name in ns for k,ns in select.items())]
def get(e):
 u='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']; b=urllib.request.urlopen(u,timeout=45).read();assert len(b)==e['size'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha'];p=OWN/'packet/private/upstream'/e['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'canonical':e,'url':u,'sha256':hashlib.sha256(b).hexdigest(),'local':str(p.relative_to(OWN/'packet')),'read_extent':'See reading-limits.md; acquisition alone is not reading'}
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:r=list(pool.map(get,es))
(OWN/'packet/public/canonical.json').write_text(json.dumps(r,indent=2)); print('Acquired and blob-verified',len(r));print('\n'.join(str(Path(z['local']).relative_to('private/upstream/preprints')) for z in r))
