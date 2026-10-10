"""Development-only primary retrieval, never imported by the offline verifier."""
from pathlib import Path
import hashlib, json, urllib.request, importlib.util, datetime
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i134_discrete_geometric_optimization'
spec=importlib.util.spec_from_file_location('html_view',ROOT/'frontier/experiments/i131_soft_summary_stability/extract_html.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
out=S/'external';out.mkdir(exist_ok=True)
records=[]
for paper,version in [('2511.03353','v1'),('2604.13355','v1'),('2607.28429','v2')]:
 for kind,suffix in [('abs',''),('html',version)]:
  url=f'https://arxiv.org/{kind}/{paper}{suffix}'
  r={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=45) as response:
    data=response.read();r.update(status=response.status,final_url=response.url)
   p=out/f'{paper}-{kind}{suffix}.html';p.write_bytes(data)
   t=p.with_suffix('.txt');t.write_text(mod.extract(data.decode()))
   r.update(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),text=str(t.relative_to(ROOT)),text_sha256=hashlib.sha256(t.read_bytes()).hexdigest(),lines=len(t.read_text().splitlines()))
  except Exception as e:r.update(error=repr(e))
  records.append(r)
  print(json.dumps(r),flush=True)
(S/'external-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
