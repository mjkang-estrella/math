import json,pathlib,re,urllib.request,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1];out=[]
def get(u,name):
 with urllib.request.urlopen(u,timeout=20) as f:b=f.read();s=f.status
 (L/f'sources/{name}').write_bytes(b)
 out.append(dict(url=u,status=s,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 return json.loads(b)
d=get('https://api.github.com/repos/openai/math/git/trees/4eaee87548250b2682affda7d05d947c05554bae','openai-root.json')
a=next(x for x in d['tree'] if x['path']=='preprints')
p=get(a['url']+'?recursive=1','openai-preprints.json')
for x in p['tree']:
 if re.search('Kazhdan',x['path'],re.I):print(x['path'])
d=json.loads((L/'sources/omega-tree.json').read_text());print('OMEGA',len(d['tree']),d.get('truncated'))
ids=json.loads((L/'reservation.json').read_text())['ids']
matches=[]
for x in d['tree']:
 if any(re.search(r'(?<!\d)'+str(i)+r'(?!\d)',x['path']) for i in ids) or re.search('Bernstein|subcube|polychrom|Hall.Paige|Kneser|Kazhdan|Garland|sunflower|Biadjoint|Tight.Tree',x['path'],re.I):
  matches.append(x)
print('MATCHES',json.dumps(matches))
(L/'outputs/registry-path-screen.json').write_text(json.dumps(dict(receipts=out,omega_truncated=d.get('truncated'),omega_matches=matches,limits='Path screen only; no blanket semantic proof clearance'),indent=2))
