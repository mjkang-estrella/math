from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r168');T=json.loads(Path('sources/preprints-tree.json').read_bytes());pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
roots={'had':'preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/build/','cdv':'preprints/A-counterexample-to-the-Colin-de-Verdiere-chromatic-conjecture-September-23-2026/build/','list':'preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/build/'}
items=[]
for tag,prefix in roots.items():
 for x in T['tree']:
  s=x['path'].casefold()
  if not s.startswith(prefix.casefold()) or x['type']!='blob':continue
  tail=x['path'][len(prefix):]
  if tag=='list' or tail in ['main.tex','preamble.tex','sections/01-introduction.tex','sections/01-history.tex','sections/13-graph-transfer.tex','sections/matrix-rank.tex','sections/matrix-trees.tex','sources/references.bib']:items.append((tag,tail,x))
def get(item):
 tag,tail,x=item;p=R/'private/source'/tag/tail;p.parent.mkdir(parents=True,exist_ok=True)
 url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+x['path']
 b=urllib.request.urlopen(url,timeout=45).read();g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert len(b)==x['size'] and g==x['sha'];p.write_bytes(b)
 return {'path':x['path'],'size':len(b),'git_blob':g,'sha256':hashlib.sha256(b).hexdigest(),'url':url,'local':str(p.relative_to(R))}
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool: rec=list(pool.map(get,items))
(R/'private/source/authentication.json').write_text(json.dumps(rec,indent=2));print('Authenticated',len(rec),'objects')
for tag in roots:
 for tail in ['main.tex','sections/01-introduction.tex']:
  p=R/'private/source'/tag/tail;print('\nREAD',p);print(p.read_text())
