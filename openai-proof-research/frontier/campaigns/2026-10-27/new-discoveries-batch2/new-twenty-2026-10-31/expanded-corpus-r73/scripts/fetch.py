import pathlib,json,hashlib,datetime,urllib.request,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
def get(key,url):
 p=D/'sources'/key; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=25) as r: data=r.read(); status=r.status; final=r.url
  p.write_bytes(data); rec=dict(url=url,final_url=final,status=status,utc=now,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
 except Exception as e:rec=dict(url=url,utc=now,error=str(e))
 (D/'sources'/f'{key}.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status',rec.get('error')),rec.get('bytes'),flush=True)
if __name__=='__main__':
 x=json.loads((D/'extracted.json').read_text())
 todo=[('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')] if 'heads' in sys.argv else []
 seen=set()
 for o in x.values():
  a=o['source_url'].split('/abs/',1)[-1]
  if a in seen: continue
  seen.add(a); k=a.replace('/','_')
  if 'eprint' in sys.argv: todo.append((k+'.eprint','https://arxiv.org/e-print/'+a))
 for k,u in todo: get(k,u); time.sleep(1.5)
