import pathlib,json,urllib.request,hashlib,datetime,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
def get(key,url):
 d=D/'downloads'/key; d.mkdir(parents=True,exist_ok=True); p=d/'file.pdf'; rp=d/'receipt.json'
 if rp.exists(): return
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source check'}),timeout=30) as r: data=r.read();rec.update(status=r.status,final_url=r.url)
  p.write_bytes(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
 except Exception as e:rec['error']=str(e)
 rp.write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status',rec.get('error')),rec.get('bytes'),flush=True)
for a in sys.argv[1:]:
 get(a.replace('/','_'),'https://arxiv.org/pdf/'+a); time.sleep(3)
