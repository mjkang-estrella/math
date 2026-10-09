#!/usr/bin/env python3
"""Independent integrity and immutable re-fetch; not a proof verifier."""
import concurrent.futures, hashlib, json, pathlib, urllib.request
ROOT=pathlib.Path(__file__).resolve().parents[3]
HERE=pathlib.Path(__file__).resolve().parent
AUTHOR=ROOT/'frontier/sources/i05_parity_pd'
sha=lambda b:hashlib.sha256(b).hexdigest()
blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
m=json.loads((AUTHOR/'manifest.json').read_text())
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())
assert not tree['truncated']
blobs={r['path']:r['sha'] for r in tree['tree']}
out={'pin':m['pin'],'tree_truncated':tree['truncated'],'upstream':[],'external':[],'author_artifacts':[],'inputs':{},'fresh':[]}
for r in m['upstream']:
 b=(AUTHOR/r['local']).read_bytes()
 ok=sha(b)==r['sha256'] and blob(b)==r['git_blob']==blobs[r['path']] and len(b)==r['bytes'] and m['pin'] in r['url']
 out['upstream'].append({'path':r['path'],'sha256':sha(b),'git_blob':blob(b),'bytes':len(b),'ok':ok})
for r in m['external']:
 if 'error' in r: out['external'].append(r);continue
 b=(AUTHOR/r['local']).read_bytes()
 out['external'].append(dict(r,ok=sha(b)==r['sha256'],is_pdf=b.startswith(b'%PDF')))
for r in json.loads((AUTHOR/'artifact-manifest.json').read_text())['artifacts']:
 b=(ROOT/r['path']).read_bytes();out['author_artifacts'].append({'path':r['path'],'ok':len(b)==r['bytes'] and sha(b)==r['sha256'],'sha256':sha(b)})
inputs=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/iterations/i05-parity-pd.md','frontier/iterations/i05-parent-screen.md','frontier/iterations/README.md','frontier/findings/R006-progression-PD-primitive-root-density.md','frontier/iterations/i03-arithmetic-progressions.md','frontier/reviews/i03-arithmetic-progressions-r4.md','frontier/experiments/i05_parity_pd/check.py','frontier/experiments/i05_parity_pd/results.json','frontier/sources/i05_parity_pd/manifest.json','frontier/sources/i05_parity_pd/validation.json','frontier/sources/i05_parity_pd/artifact-manifest.json']
for p in inputs:
 b=(ROOT/p).read_bytes();out['inputs'][p]={'sha256':sha(b),'bytes':len(b)}
selected=[]
for r in m['upstream']:
 p=r['path']
 if ('The-Poisson' in p and any('/'+s in p for s in ['02-preliminaries.tex','03-determinant.tex','04-memory.tex','05-major-arcs.tex','06-correlations.tex','07-extraction.tex','08-poisson-dirichlet.tex','09-long-prime-appendix.tex'])) or ('Primitive-roots-for-every' in p and p.endswith('08-type-ii.tex')) or ('Weighted-Dilation' in p and p.endswith('02-transference.tex')) or ('Prime-Predecessors-with' in p and (p.endswith('03-shifted.tex') or p.endswith('main.tex'))) or ('Simultaneous-primitive' in p and p.endswith('04-marked-family.tex')) or ('Ordinary-two-point' in p):selected.append(r)
def fetch(r):
 try:
  with urllib.request.urlopen(r['url'],timeout=35) as response:b=response.read()
  (HERE/r['local']).write_bytes(b)
  return {'url':r['url'],'local':r['local'],'sha256':sha(b),'git_blob':blob(b),'bytes':len(b),'ok':b==(AUTHOR/r['local']).read_bytes() and blob(b)==blobs[r['path']]}
 except Exception as e:return {'url':r['url'],'error':str(e),'ok':False}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:out['fresh']=list(ex.map(fetch,selected))
out['summary']={'pinned':len(out['upstream']),'fresh':len(out['fresh']),'artifacts':len(out['author_artifacts']),'passed':all(r['ok'] for key in ['upstream','fresh','author_artifacts'] for r in out[key]) and all(r.get('ok',True) for r in out['external'])}
(HERE/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out['summary'],indent=2))
