import pathlib,json,urllib.request,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]
def get(key,url):
 p=D/'sources'/key; rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if (D/'sources'/f'{key}.receipt.json').exists(): return
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source check'}),timeout=15) as r: data=r.read();rec.update(status=r.status,final_url=r.url)
  p.write_bytes(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
 except Exception as e:rec['error']=str(e)
 (D/'sources'/f'{key}.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status',rec.get('error')),flush=True)
if __name__=='__main__':
 if len(sys.argv)>1:get(sys.argv[1],sys.argv[2])
 else:
  get('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD');get('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')
  for a in dict.fromkeys(o['source_url'].rsplit('/',1)[-1] for o in json.loads((D/'extracted.json').read_text()).values()):get(a+'.abs.html','https://arxiv.org/abs/'+a)
