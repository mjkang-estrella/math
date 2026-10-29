import pathlib,json,hashlib,shutil
L=pathlib.Path(__file__).resolve().parent
S=L.parent/'sol-fresh-source-discovery-r108'
out=[]
for name in ['refresh-http.json','refresh.log','sources/omega-delta.json','sources/omega-HEAD.json']:
 p=S/name;h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 dst=L/'inputs/registry'/name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
 row=dict(path=str(p),sha256=h.hexdigest(),bytes=p.stat().st_size)
 if name.endswith('omega-delta.json'):
  d=json.loads(p.read_text());row.update(total_commits=d.get('total_commits'),files=[x['filename'] for x in d['files']])
 out.append(row)
(L/'registry-receipts.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out[2]))
