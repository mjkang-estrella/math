import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,shutil,urllib.request,datetime,subprocess,concurrent.futures
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i51_hard_moment_quantitative_stability_novelty'; A=R/'frontier/sources/i49_hard_moment_quantitative_stability'
sha=lambda b:hashlib.sha256(b).hexdigest()
paths=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json','frontier/iterations/i49-hard-moment-quantitative-stability.md','frontier/iterations/i46-quantitative-logarithmic-stability.md','frontier/iterations/i44-logarithmic-equality-polytopes.md','frontier/reviews/i45-logarithmic-equality-r2.md','frontier/reviews/i47-planar-logarithmic-stability-r2.md','frontier/reviews/i48-planar-logarithmic-stability-novelty.md','frontier/experiments/i49-parent-verification.json','frontier/iterations/iteration51-hard-moment-quantitative-stability-novelty-task.json']
paths+=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
paths+=[str(p.relative_to(R)) for p in A.glob('*.json')]+[str((A/'brief.txt').relative_to(R))]
paths+=[str(p.relative_to(R)) for p in (R/'frontier/experiments/i49_hard_moment_quantitative_stability').glob('*.py')]
paths+=[x['path'] for x in json.loads((A/'prior-seals.json').read_text())]
# Only selected existing upstream sources, never recursive archives.
paths+=[str(p.relative_to(R)) for p in (A/'pinned').rglob('*') if p.is_file()]
rows=[]
for f in dict.fromkeys(paths):
 b=(R/f).read_bytes();p=S/'frozen'/f;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 rows.append(dict(path=f,copy=str(p.relative_to(S)),bytes=len(b),sha256=sha(b),mutable=f in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'] or 'iteration51-' in f))
(S/'frozen-inputs.json').write_text(json.dumps(rows,indent=2)+'\n')
task=json.loads((R/paths[13]).read_text())
(S/'brief.txt').write_text(task['brief'])
old=json.loads((A/'responses.json').read_text())
requests=[(x['url'],x['file']) for x in old]
for name,id in [('bd','2101.02549'),('lu','2608.20730'),('xi','2307.04266'),('wang','2510.19061'),('he-liu','2510.21530')]:requests.append((f'https://arxiv.org/abs/{id}',f'primary/{name}-current.html'))
def fetch(item):
 url,file=item;p=S/file;p.parent.mkdir(parents=True,exist_ok=True);r=dict(url=url,file=file,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research evidence review'}),timeout=45) as res:b=res.read();r.update(status=res.status,final_url=res.url,headers=dict(res.headers),ok=True)
 except Exception as e:b=str(e).encode();r.update(ok=False,error=repr(e))
 p.write_bytes(b);r.update(bytes=len(b),sha256=sha(b))
 if b.startswith(b'%PDF'):
  run=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True);p.with_suffix('.txt').write_bytes(run.stdout);r.update(pdftotext_returncode=run.returncode,text_sha256=sha(run.stdout))
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:responses=list(ex.map(fetch,requests))
(S/'responses.json').write_text(json.dumps(responses,indent=2)+'\n')
print(json.dumps({'frozen':len(rows),'responses':len(responses),'successes':sum(x['ok'] for x in responses),'failures':[x for x in responses if not x['ok']]}))
