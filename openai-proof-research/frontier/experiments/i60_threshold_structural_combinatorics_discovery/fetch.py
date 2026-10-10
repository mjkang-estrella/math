from pathlib import Path
import urllib.request,json,hashlib,datetime,concurrent.futures,subprocess
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i60_threshold_structural_combinatorics_discovery';D=S/'literature';D.mkdir(exist_ok=True)
urls={
'filmus-mossel-abs':'https://arxiv.org/abs/1507.02713',
'filmus-mossel-pdf':'https://arxiv.org/pdf/1507.02713',
'filmus-basis-abs':'https://arxiv.org/abs/1406.0142',
'filmus-basis-pdf':'https://arxiv.org/pdf/1406.0142',
'ahpt-abs':'https://arxiv.org/abs/2608.11183',
'ahpt-pdf':'https://arxiv.org/pdf/2608.11183',
'yang-abs':'https://arxiv.org/abs/2609.20864',
'yang-pdf':'https://arxiv.org/pdf/2609.20864',
'li-abs':'https://arxiv.org/abs/2609.08967',
'li-pdf':'https://arxiv.org/pdf/2609.08967',
'park-abs':'https://arxiv.org/abs/2609.14681',
'park-pdf':'https://arxiv.org/pdf/2609.14681',
'mathdb':'https://www.mathdb.org/',
}
def fetch(item):
 name,url=item;r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=35) as resp:
   b=resp.read();r.update(status=resp.status,final_url=resp.url,headers=dict(resp.headers))
  path=D/(name+('.pdf' if b.startswith(b'%PDF') else '.html'));path.write_bytes(b)
  r.update(file=str(path.relative_to(ROOT)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF'):
   out=path.with_suffix('.txt');p=subprocess.run(['pdftotext','-layout',str(path),str(out)],capture_output=True,text=True);r.update(extract_exit=p.returncode,extract_stderr=p.stderr)
   if out.exists():r.update(text=str(out.relative_to(ROOT)),text_sha256=hashlib.sha256(out.read_bytes()).hexdigest())
 except Exception as e:r.update(error=repr(e))
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool: rows=list(pool.map(fetch,urls.items()))
(D/'responses.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['name','status','bytes','error'] if k in r} for r in rows],indent=2))
