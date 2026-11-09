exec((__import__('pathlib').Path(__file__).with_name('work.py')).read_text().split("if sys.argv[1]=='init':")[0])
def fetch(url,name):
 d=L/'sources'/name;d.parent.mkdir(exist_ok=True)
 if d.exists():return d
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'MathematicsResearch/1.0'})
  with urllib.request.urlopen(req,timeout=22) as r:
   data=r.read(8*1024*1024);rec.update(status=r.status,final_url=r.url)
  d.write_bytes(data);rec.update(sha256=sha(d),bytes=len(data),file=str(d))
 except Exception as e:rec['failure']=str(e)
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return d if d.exists() else None
if __name__=='__main__':
 for url,name in zip(sys.argv[1::2],sys.argv[2::2]):
  p=fetch(url,name);print(name,p)
  if p and p.suffix!='.pdf':print(p.read_text(errors='replace')[:45000])
