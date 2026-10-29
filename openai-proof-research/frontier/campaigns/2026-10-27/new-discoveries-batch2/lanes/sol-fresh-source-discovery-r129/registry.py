import json,pathlib,urllib.request,hashlib,datetime
L=pathlib.Path(__file__).parent;S=L/'sources';head=json.loads((S/'omega-default.json').read_text());d=json.loads((S/'omega-default-delta.json').read_text())
r={'observed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'omega_head':head['sha'],'omega_commit_date':head['commit']['committer']['date'],'openai_head':json.loads((S/'openai-head.json').read_text())['sha'],'base':'9a026fe5527cacf8d3aed5f9291f08bc520ea90b','status':d['status'],'ahead':d['ahead_by'],'behind':d['behind_by'],'total_commits':d['total_commits'],'commits_returned':len(d['commits']),'files_returned':len(d['files']),'api_cap_detected':len(d['commits'])!=d['total_commits'] or len(d['files'])>=300,'scope':'bounded delta only; inherited r3/r4 receipts not semantic target clearance; wrong main branch response retained separately','bodies':[]}
for i,f in enumerate(d['files']):
 if not f['filename'].endswith(('.md','.lean')):continue
 url='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head['sha']+'/'+f['filename']
 rec={'url':url,'path':f['filename'],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as resp:b=resp.read();rec['status']=resp.status
  dest=S/('delta-%02d'%i+pathlib.Path(f['filename']).suffix);dest.write_bytes(b);rec.update(file=dest.name,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:rec['error']=str(e)
 r['bodies'].append(rec)
(S/'registry-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='bodies'}))
