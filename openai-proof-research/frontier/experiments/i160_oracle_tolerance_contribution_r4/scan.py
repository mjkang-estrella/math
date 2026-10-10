import json,hashlib,re,time
from pathlib import Path
S=Path('frontier/sources/i160_oracle_tolerance_contribution_r4'); assert not (S/'seal.json').exists()
def load(p):return json.loads(Path(p).read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,v):(S/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
dp='frontier/sources/i112_inverse_boundary_discovery/search-domain.json';tp='frontier/sources/i112_inverse_boundary_discovery/snapshots/sources/preprints-tree.json';domain=load(dp);tree=load(tp)['tree']; blobs={x['path']:x for x in tree if x['type']=='blob'}
assert len(tree)==13223 and len(blobs)==len(domain)==10373
patterns={'robust':r'(?i)(?:robust|noisy|inexact|inaccurate|adversarial|adaptive|biased|perturbation).{0,70}(?:sampl|oracle|gradient)|(?:sampl|oracle|gradient).{0,70}(?:robust|inexact|inaccurate|adversarial|biased)', 'entropy':r'(?i)shifted.composition|log.Harnack|relative.entropy|KL.divergence', 'compiler':r'(?i)fixed.seed|coefficient.sum|routine.height|Gaussian.reserve|reserved.noise|uncached|compiler.lipschitz|small.coefficients'}
rx={k:re.compile(v) for k,v in patterns.items()};hits={k:[] for k in rx};bind=[];t=time.time()
for x in domain:
 b=Path(x['local']).read_bytes();o=b if x['local']==x['original_local'] else Path(x['original_local']).read_bytes()
 assert sha(b)==x['sha256'] and sha(o)==x['original_sha256'],x['path']
 assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']==blobs[x['path']]['sha']
 bind.append(x)
 for i,l in enumerate(b.decode('utf8','replace').splitlines(),1):
  for k,r in rx.items():
   m=list(r.finditer(l))
   if m:hits[k].append(dict(path=x['path'],local=x['local'],line=i,text=l,spans=[list(z.span()) for z in m]))
assert sum(x['kind']=='outside_pdf' for x in domain)==776
save('corpus.json',dict(tree_path=tp,domain_path=dp,tree_entries=len(tree),manuscripts=sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree),original_blob_positions=len(domain),pdf_text_bindings=776,bindings=bind,preparation_traversals=1,elapsed_seconds=time.time()-t))
save('search.json',dict(patterns=patterns,results=hits,convention='UTF8 replacement decode; Python splitlines; zero-based codepoint spans; ordered occurrences, no deduplication'))
prior=[];r=re.compile(r'(?i)log.concave|adversarial.oracle|oracle.tolerance|shifted.composition|smoothed.Picard|inexact.gradient')
for p in sorted(Path('frontier/iterations').glob('i*.md')):
 if re.match(r'i(15[5-8]|16[0-9])[-_]',p.name):continue
 b=p.read_bytes(); rows=[]
 for i,l in enumerate(b.decode().splitlines(),1):
  m=list(r.finditer(l))
  if m:rows.append(dict(line=i,text=l,spans=[list(z.span()) for z in m]))
 if rows:prior.append(dict(path=str(p),sha256=sha(b),hits=rows))
save('prior-search.json',dict(expression=r.pattern,results=prior,scope='Prior iteration reports; active I158 excluded; only matching reports bound'))
print(json.dumps(dict(counts={k:len(v) for k,v in hits.items()},prior_reports=[x['path'] for x in prior],elapsed=time.time()-t)))
