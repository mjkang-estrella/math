import json,pathlib,urllib.request,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
repo='the-omega-institute/trureturing';head=json.loads((L/'sources/registry-trureturing.html').read_text())
def get(name,url):
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as r:b=r.read();rec.update(status=r.status,sha256=hashlib.sha256(b).hexdigest())
  (L/f'sources/{name}.json').write_bytes(b);v=json.loads(b)
 except Exception as e:rec['error']=str(e);v={}
 (L/f'sources/{name}-receipt.json').write_text(json.dumps(rec,indent=2));return v
root=get('omega-root',f'https://api.github.com/repos/{repo}/git/trees/{head["commit"]["tree"]["sha"]}')
ids=list(json.loads((L/'extracted.json').read_text()))
report={}
for x in root.get('tree',[]):
 if x['path'] in ['D5','Problems']:
  tree=get('omega-'+x['path'],f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1')
  report[x['path']]={'truncated':tree.get('truncated'),'matches':[t for t in tree.get('tree',[]) if any(k in t['path'] for k in ids)]}
(L/'outputs/registry-screen.json').write_text(json.dumps(report,indent=2));print(report)
