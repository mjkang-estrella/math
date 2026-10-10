from pathlib import Path
import urllib.request,json,hashlib,datetime
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i142_uniform_algebraic_allocation';P=S/'primary'
ns={};source=(R/'frontier/experiments/i142_uniform_algebraic_allocation/fetch_primary.py').read_text();exec(source[source.index('class Extract'):source.index('urls=')],dict(HTMLParser=__import__('html.parser',fromlist=['HTMLParser']).HTMLParser),ns);Extract=ns['Extract']
urls={'trusiani-abs':'https://arxiv.org/abs/1804.02306','trusiani-current':'https://arxiv.org/html/1804.02306','jets2026-abs':'https://arxiv.org/abs/2605.25185','jets2026-current':'https://arxiv.org/html/2605.25185'}
records=json.loads((P/'retrievals.json').read_text());assert not(S/'seal.json').exists()
for name,url in urls.items():
 rec=dict(name=name,url=url,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  b=urllib.request.urlopen(url,timeout=40).read();(P/(name+'.html')).write_bytes(b);p=Extract();p.feed(b.decode());ls=[' '.join(l.split()) for l in ''.join(p.out).splitlines()];t='\n'.join(l for l in ls if l)+'\n';(P/(name+'.txt')).write_text(t);rec.update(sha256=hashlib.sha256(b).hexdigest(),lines=len(t.splitlines()))
 except Exception as e:rec['failure']=repr(e)
 records.append(rec)
(P/'retrievals.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records[-4:],indent=2))
