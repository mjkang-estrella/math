from pathlib import Path
import hashlib,json,resource,subprocess,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
b=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
o=b/'lanes/sol-log-arctangent-investment-review-r3';o.mkdir(exist_ok=True)
names=['root-log-arctangent-candidate-r1','root-log-arctangent-certificate-r2','root-log-arctangent-source-r3','sol-log-arctangent-preliminary-review-r1','sol-log-arctangent-source-subsumption-r1','sol-log-arctangent-derivative-review-r2','sol-cascade-rate-preliminary-review-r1']
h={}
for n in names:
 for p in sorted((b/'lanes'/n).rglob('*')):
  if p.is_file():h[str(p.relative_to(b))]=hashlib.sha256(p.read_bytes()).hexdigest()
for n in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 p=b/n;h[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(o/'hash-before.json').write_text(json.dumps(h,indent=2)+'\n')
checks={}
for n in names[:3]:
 p=b/'lanes'/n
 manifest=p/('provenance.json' if n.endswith('source-r3') else 'review-freeze.json')
 m=json.loads(manifest.read_text())
 hashes=m.get('hashes',m.get('files'))
 print(n, type(hashes),str(hashes)[:150])
 if isinstance(hashes,dict):
  checks[n]={f:hashlib.sha256((p/f).read_bytes()).hexdigest()==v for f,v in hashes.items()}
  assert all(checks[n].values())
(o/'manifest-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
pdf=b/'lanes/root-log-arctangent-source-r3/sources/publisher-canonical.pdf'
for page in [1,2,4,21]:
 subprocess.run(['pdftoppm','-f',str(page),'-l',str(page),'-scale-to','1500','-singlefile','-png',str(pdf),str(o/f'published-page{page}')],check=True,timeout=15)
print('before hashes',len(h),'rendered four pages')
