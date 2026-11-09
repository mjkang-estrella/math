import pathlib,json,urllib.request,hashlib,datetime,re
L=pathlib.Path(__file__).resolve().parents[1];rs=[]
def fetch(name,url):
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence'}),timeout=20) as s:d=s.read();status=s.status
  (L/'sources'/name).write_bytes(d);rs.append(dict(file=name,url=url,status=status,sha256=hashlib.sha256(d).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
  (L/'outputs/registry-finish-receipts.json').write_text(json.dumps(rs,indent=2));return json.loads(d)
 except Exception as e:
  rs.append(dict(file=name,url=url,error=str(e)));(L/'outputs/registry-finish-receipts.json').write_text(json.dumps(rs,indent=2));return {}
sha=json.loads((L/'sources/omega-head').read_text())['sha'];base='https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'
root=fetch('omega-root.json',base+sha)
for name in ['D5','Problems']:
 x=next((x for x in root.get('tree',[]) if x['path']==name),None)
 if x:
  t=fetch('omega-'+name+'.json',base+x['sha']+'?recursive=1')
  print(name,'truncated',t.get('truncated'),'entries',len(t.get('tree',[])))
  for x in t.get('tree',[]):
   if re.search('word.?represent|toroid|cylind|grid',x['path'],re.I):print(name,x['path'],x['sha'])
