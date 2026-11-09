from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,sys
R=Path(__file__).resolve().parent
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ResearchReview/1.0'}),timeout=30) as f:b=f.read(15000000);status=f.status;final=f.url
 except urllib.error.HTTPError as e:b=e.read();status=e.code;final=e.url
 except Exception as e:
  rec={'utc':t,'url':url,'error':str(e)}
  with (R/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec);continue
 (R/name).write_bytes(b);rec={'utc':t,'url':url,'status':status,'final_url':final,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'file':name}
 with (R/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec)
