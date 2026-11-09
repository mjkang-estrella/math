import pathlib,urllib.request,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1]
def get(name,url):
 r={'url':url,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research source verification'}),timeout=25) as f: b=f.read();r['status']=f.status
  (D/'sources'/name).write_bytes(b);r['sha256']=hashlib.sha256(b).hexdigest()
 except Exception as e:r['error']=str(e)
 (D/'sources'/(name+'.receipt.json')).write_text(json.dumps(r,indent=2));print(r,flush=True)
 return r
get('arxiv-abs.html','https://arxiv.org/abs/2404.18517')
r=get('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')
if 'sha256' in r:
 h=json.loads((D/'sources/omega-head.json').read_text())['sha']
 for name,path in [('omega-problem.md','Problems/chenkitaevzhang-2024-separable-record-peak-three.md')]+[(x+'.lean','D5/S1/Words/Patterns/Separable/'+x+'.lean') for x in ['RecordPeak','RecordFirstDecline','RecordNewtonPositivity','RecordTransport']]:get(name,f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/{path}')
