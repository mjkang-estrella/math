import pathlib,json,urllib.request,datetime,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];rec=[]
def get(url,name):
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research'}),timeout=20) as r:b=r.read();status=r.status
 (D/'sources'/name).write_bytes(b);rec.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':status,'sha256':hashlib.sha256(b).hexdigest()});return json.loads(b)
sha=json.loads((D/'sources/omega-head.json').read_text())['sha'];base='https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'
root=get(base+sha,'omega-root.json');paths=[]
for scope in ['D5','Problems']:
 row=next(x for x in root['tree'] if x['path']==scope);j=get(base+row['sha']+'?recursive=1','omega-'+scope+'.json');assert not j.get('truncated');paths += [scope+'/'+x['path'] for x in j['tree']]
terms=['Dickson','diamond','Schur','minuscule','pentagraph','hyperoval','Frobenius','Bruhat','Laugesen','simplicial','primitive','Eulerian','progression','Waring','HamiltonBerge','cyclotomic','Cosine']
match=[p for p in paths if any(t.lower() in p.lower() for t in terms)];(D/'outputs/registry-path-screen.json').write_text(json.dumps({'head':sha,'scope':'complete D5 and Problems paths only; bodies unread','terms':terms,'matches':match},indent=2)+'\n');(D/'sources/registry-receipts.json').write_text(json.dumps(rec,indent=2)+'\n');print('\n'.join(match))
