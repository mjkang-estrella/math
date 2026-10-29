exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('jobs=')[0])
from html.parser import HTMLParser
from math import comb
h=json.loads((L/'sources/peak-head.json').read_text());sha=h['sha'];print('peak',sha,h['commit']['committer']['date'])
print('files',[(f['filename']) for f in h['files']])
jobs={}
for f in h['files']:
 if f['filename'].lower().endswith(('.md','.tex','.py')):jobs['peak-'+f['filename'].replace('/','_')]='https://raw.githubusercontent.com/fengqiaoqu/plactic-peak-counterexample/'+sha+'/'+f['filename']
r=json.loads((L/'http.json').read_text())
for name,url in jobs.items():
 x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(2000000);x.update(status=f.status,final_url=f.url)
  (L/'sources'/name).write_bytes(b);x.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:x['error']=str(e)
 r.append(x)
(L/'http.json').write_text(json.dumps(r,indent=2))
class Parser(HTMLParser):
 def handle_data(self,d):self.parts.append(d)
p=L/'sources/properties.html';parser=Parser();parser.parts=[];parser.feed(p.read_text());p.with_suffix('.html.txt').write_text(' '.join(parser.parts))
# Exact ULC check, a stronger diagnostic only.
d=json.loads((L/'analysis-results.json').read_text());tested=0;bad=[]
for r in d['rows']:
 n=r['n'];a=r['a']
 for k in range(2,n-1):
  tested+=1
  if a[k]**2*comb(n-2,k-2)*comb(n-2,k)<a[k-1]*a[k+1]*comb(n-2,k-1)**2:bad.append([n,k])
(L/'ulc-results.json').write_text(json.dumps({'tested':tested,'failures':bad},indent=2));print('ULC',tested,bad)
