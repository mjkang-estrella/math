import pathlib,json,urllib.request,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]
x=list(json.loads((D/'extracted.json').read_text()).values())
todo=[]
if sys.argv[1]=='registry':
 todo=[('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')]
else:
 for o in x[int(sys.argv[1]):int(sys.argv[2])]:
  a=o['source_url'].rsplit('/',1)[-1]
  todo += [(str(o['mathdb_id'])+'.abs.html',o['source_url']), (str(o['mathdb_id'])+'.pdf','https://arxiv.org/pdf/'+a)]
for key,url in todo:
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source check'}),timeout=9) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(D/'sources'/key).write_bytes(data)
 except Exception as e:rec['error']=str(e)
 (D/'sources'/(key+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(key,rec,flush=True)
