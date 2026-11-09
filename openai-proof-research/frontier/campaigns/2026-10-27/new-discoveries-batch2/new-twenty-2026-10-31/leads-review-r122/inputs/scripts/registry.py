import pathlib,json,runpy
D=pathlib.Path(__file__).resolve().parents[1]
# Read-only public HTTP; pin all bodies to current observed commit.
import urllib.request,hashlib,datetime

def get(key,url):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=12) as f:b=f.read(30000000);r['status']=f.status
  (D/'sources'/key).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:r['error']=str(e)
 (D/'sources'/(key+'.receipt.json')).write_text(json.dumps(r,indent=2));return json.loads(b) if r.get('status')==200 and key.endswith('.json') else None
sha=json.loads((D/'sources/omega-head.json').read_text())['sha'];base='https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'
x=get('omega-root.json',base+sha)
if x:
 for ent in x['tree']:
  if ent['path'] in ['D5','Problems']:get('omega-'+ent['path']+'.json',base+ent['sha']+'?recursive=1')
get('omega-pseudopaley.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/'+sha+'/D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.lean')
get('tang-2609.25102-abs.html','https://arxiv.org/abs/2609.25102')
get('tang-2609.25102v1.pdf','https://arxiv.org/pdf/2609.25102v1')
get('ballot-2102.08508v1.pdf','https://arxiv.org/pdf/2102.08508v1')
print('done')
