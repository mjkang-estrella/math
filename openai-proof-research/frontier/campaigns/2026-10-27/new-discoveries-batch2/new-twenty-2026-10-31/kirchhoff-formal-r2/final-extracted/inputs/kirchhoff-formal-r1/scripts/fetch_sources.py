from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime
D=Path(__file__).resolve().parents[1]
urls={
 'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD',
 'omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
 'arxiv-v2':'https://arxiv.org/html/2101.07103v2',
 'estrada-publications':'https://sites.google.com/view/ernestoestrada/publications',
 'mugnolo-publications':'https://www.fernuni-hagen.de/analysis/docs/lebenslauf_mugnolo.pdf',
 'later-advection':'https://www.mmnp-journal.org/articles/mmnp/pdf/2022/01/mmnp210285.pdf',
 'published-author-copy':'https://www.fernuni-hagen.de/analysis/docs/estrada_mugnolo.pdf'
}
for name,url in urls.items():
 p=D/'sources'/name
 if (D/'receipts'/f'{name}.json').exists():continue
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-fidelity-check/1.0'}),timeout=25) as r:
   b=r.read();p.write_bytes(b);receipt.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:receipt.update(error=str(e),status=getattr(e,'code',None),not_retried=True)
 (D/'receipts'/f'{name}.json').write_text(json.dumps(receipt,indent=2));print(name,receipt.get('status'),receipt.get('error',''))
