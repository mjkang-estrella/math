from pathlib import Path
import urllib.request,json,hashlib,datetime,re
b=Path(__file__).resolve().parent;(b/'live').mkdir(exist_ok=True);logs=[]
def fetch(name,url):
 x={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'independent-math-review'}),timeout=25) as r:data=r.read(16000000);x.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest())
  (b/'live'/name).write_bytes(data);logs.append(x);return data
 except Exception as e:x['error']=str(e);logs.append(x);return None
for repo,n in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
 data=fetch(n+'-head.json',f'https://api.github.com/repos/{repo}/commits?per_page=1')
 if data:
  h=json.loads(data)[0]['sha'];base='0292f3378609092ee734f5a57f64cdfc137695b0' if n=='omega' else '7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'
  print(n,h,json.loads(data)[0]['commit']['committer']['date'])
  if h!=base:fetch(n+'-compare.json',f'https://api.github.com/repos/{repo}/compare/{base}...{h}')
fetch('he-research.html','https://www.engineering.uwaterloo.ca/~q7he/research.html')
(b/'http.json').write_text(json.dumps(logs,indent=2))
# Read all counting standards and exclusions, store compact actual bodies.
c=json.loads((b/'context.json').read_text());d=next(z['data'] for p,z in c.items() if p.endswith('/ledger.json'))
e=next(z['data'] for p,z in c.items() if p.endswith('/prior-campaign-context.json'))
r={k:d[k] for k in ['counting_standard','acceptance_gates','excluded','baseline']};r['prior_excluded']=e['excluded'];r['held_candidates']=e['held_candidates'];(b/'counting-exclusions.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2)[:20000])
