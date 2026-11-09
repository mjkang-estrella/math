from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,sys
L=Path(__file__).resolve().parent
def fetch(url,name):
 p=L/'sources'/name;p.parent.mkdir(exist_ok=True)
 row={'url':url,'path':str(p),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source fidelity contact local scholarly client'}),timeout=35) as r:
   data=r.read(12000000);row.update(status=r.status,final_url=r.url)
  p.write_bytes(data);h=hashlib.sha256(data).hexdigest();assert hashlib.sha256(p.read_bytes()).hexdigest()==h
  row.update(sha256=h,bytes=len(data),frozen_before_read=True)
 except Exception as e:row['failure']=repr(e)
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(row)
 if 'sha256' in row and p.suffix!='.pdf':print(p.read_text(errors='replace')[:16000])
if __name__=='__main__':fetch(sys.argv[1],sys.argv[2])
