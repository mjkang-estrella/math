import pathlib,json,hashlib,datetime,urllib.request,urllib.error,sys
D=pathlib.Path(__file__).resolve().parents[1]
def get(key,url):
 p=D/'sources'/key
 if (D/'sources'/(key+'.receipt.json')).exists():return
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research'}),timeout=6) as f:b=f.read(20000000);r.update(status=f.status,final_url=f.url)
  p.write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:r.update(error=str(e))
 (D/'sources'/(key+'.receipt.json')).write_text(json.dumps(r,indent=2));print(key,r.get('status',r.get('error')),flush=True)
if sys.argv[1]=='abs':
 get('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD');get('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')
 for a in sorted({o['source_url'].split('/')[-1] for o in json.loads((D/'extracted.json').read_text()).values()}):get(a+'-abs.html','https://arxiv.org/abs/'+a)
else:
 vs=json.loads((D/'versions.json').read_text()); todo=[a+'v'+str(v) for a,vv in vs.items() for v in vv]
 for a in todo[int(sys.argv[1]):int(sys.argv[1])+12]:get(a+'.pdf','https://arxiv.org/pdf/'+a)
