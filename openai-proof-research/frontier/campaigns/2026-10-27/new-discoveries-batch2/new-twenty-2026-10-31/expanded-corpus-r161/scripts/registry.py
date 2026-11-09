import pathlib,json,urllib.request,datetime,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];o=json.loads((D/'sources/omega-head').read_text());sha=o['sha'];url=f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}?recursive=1';r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=25) as f:b=f.read();r['status']=f.status
 (D/'sources/omega-tree.json').write_bytes(b);r['sha256']=hashlib.sha256(b).hexdigest();tree=json.loads(b);r['truncated']=tree.get('truncated');paths=[x['path'] for x in tree['tree']];r['path_count']=len(paths)
 pats=['345262','345263','345415','345754','346023','346063','346267','346743','346765','347650','349325','349606','350694','352006','352266','352316','352535','352660','360151','364678','oddtown','spreading','divine','zeckendorf','grunbaum','grassmann','grassman','partial-dual','betweenness','condorcet','partition-rank']
 r['path_matches']=[p for p in paths if any(q.lower() in p.lower() for q in pats)]
except Exception as e:r['error']=str(e)
(D/'outputs/registry.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
