from pathlib import Path
import requests,json,hashlib,datetime,re
w=Path(__file__).resolve().parent;s=w/'sources'
def get(k,u):
 z=requests.get(u,timeout=25);(s/(k+'.bin')).write_bytes(z.content);(s/(k+'.receipt.json')).write_text(json.dumps(dict(url=u,status=z.status_code,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(z.content).hexdigest()),indent=2));z.raise_for_status();return z.json()
d=json.loads((s/'omega-head.bin').read_bytes());t=get('omega-root','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+d['commit']['tree']['sha']);out={}
for x in t['tree']:
 if x['path'] in ['D5','Problems']:
  a=get('omega-'+x['path'],'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+x['sha']+'?recursive=1');hits=[v['path'] for v in a['tree'] if re.search('banned|snark|ribbon|armstrong|wachspress|cactus|kriesell|neighborly|parsimony',v['path'],re.I)];out[x['path']]=dict(tree=x['sha'],truncated=a['truncated'],entries=len(a['tree']),hits=hits)
print(json.dumps(out,indent=2));(w/'registry-refreshed-screen.json').write_text(json.dumps(out,indent=2))
