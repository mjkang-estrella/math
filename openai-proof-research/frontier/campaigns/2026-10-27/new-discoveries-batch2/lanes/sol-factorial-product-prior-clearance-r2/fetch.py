import pathlib,urllib.request,json,datetime,hashlib,subprocess
O=pathlib.Path(__file__).resolve().parent
def fetch(url,name):
 r={'url':url,'utc_start':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'bounded-mathematical-review'}),timeout=35) as q:
   b=q.read(6000000);r.update(status=q.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(O/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 r['utc_end']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 with (O/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(r)
 return r
if __name__=='__main__':
 import sys
 for url,name in zip(sys.argv[1::2],sys.argv[2::2]):
  r=fetch(url,name)
  if name.endswith('.pdf') and r.get('status')==200:subprocess.run(['pdftotext','-layout',str(O/name),str(O/name).replace('.pdf','.txt')],check=True)
