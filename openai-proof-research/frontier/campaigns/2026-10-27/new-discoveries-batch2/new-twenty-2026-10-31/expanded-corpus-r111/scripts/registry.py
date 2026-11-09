import pathlib,json,urllib.request,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]; receipts=[]
def get(name,url):
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f:d=f.read();rec.update(status=f.status,sha256=hashlib.sha256(d).hexdigest(),bytes=len(d));(L/'sources'/name).write_bytes(d)
  return json.loads(d)
 except Exception as e:rec['error']=str(e)
 finally:receipts.append(rec);(L/'sources/registry-receipts.json').write_text(json.dumps(receipts,indent=2))
sha=json.loads((L/'sources/omega-head.json').read_text())['sha']; root=get('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}')
if root:
 for t in root['tree']:
  if t['path'] in ['D5','Problems']:
   data=get('omega-'+t['path']+'.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{t["sha"]}?recursive=1')
   if data:print(t['path'],len(data['tree']),'truncated',data.get('truncated'))
get('stable-zenodo.json','https://zenodo.org/api/records/22568329')
