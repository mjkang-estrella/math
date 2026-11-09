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
 x=json.loads((D/'extracted.json').read_text()); todo=[('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')]
 seen=set()
 for o in x.values():
  a=o['source_url'].rsplit('/',1)[-1]
  if 'arxiv.org' not in o['source_url']:continue
  if a not in seen:todo.append((a+'.pdf','https://arxiv.org/pdf/'+a));seen.add(a)
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
  for v in ex.map(get,todo):print(v,flush=True)
