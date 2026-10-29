import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent;B=L.parent
rows=[]
for lane,rel in [('sol-fresh-source-discovery-r100','sources/registry-delta-0.json'),('sol-fresh-source-discovery-r100','sources/registry-delta-1.json'),('sol-fresh-source-discovery-r100','sources/registry-delta-2.json'),('sol-fresh-source-discovery-r100','sources/registry-delta-3.json'),('sol-fresh-source-discovery-r100','sources/registry-delta-4.json')]:
 p=B/lane/rel;d=json.loads(p.read_bytes());rows.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'total_commits':d.get('total_commits'),'returned_commits':len(d.get('commits',[])),'files':len(d.get('files',[])),'base':d.get('base_commit',{}).get('sha'),'end':d.get('commits',[{}])[-1].get('sha')})
(L/'old-chain-cap.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
