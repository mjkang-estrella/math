import pathlib,json,hashlib,datetime,concurrent.futures,urllib.request
D=pathlib.Path(__file__).resolve().parents[1]
def get(item):
 key,url=item; p=D/'sources'/key; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=22) as r: data=r.read(); status=r.status; final=r.url
  p.write_bytes(data); rec=dict(url=url,final_url=final,status=status,utc=now,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
 except Exception as e:rec=dict(url=url,utc=now,error=str(e))
 (D/'sources'/f'{key}.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');return key,rec.get('status',rec.get('error')),rec.get('bytes')
if __name__=='__main__':
 todo=[('ferroni.pdf','https://arxiv.org/pdf/2105.04465'),('pattern-dimension.pdf','https://raulpenaguiao.github.io/docs/Mathdocs/2024feasibleregiondimension.pdf')]
 for a in todo:print(get(a),flush=True)
 o=json.loads((D/'sources/omega-head.json').read_text());sha=o['sha']
 print(get(('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}')),flush=True)
 t=json.loads((D/'sources/omega-root.json').read_text())
 for e in t.get('tree',[]):
  if e['path'] in ['D5','Problems']:
   print(get(('omega-'+e['path']+'.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+e['sha']+'?recursive=1')),flush=True)
