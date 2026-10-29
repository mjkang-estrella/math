import pathlib,json,urllib.request,hashlib,datetime,subprocess
p=pathlib.Path(__file__).parent;r=json.loads((p/'http.json').read_text())
def get(name,url):
 x={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read();x.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  (p/'sources'/name).write_bytes(b)
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(p/'sources'/name),str(p/'sources'/name.replace('.pdf','.txt'))],check=True)
  r.append(x);return b
 except Exception as e:x['error']=str(e);r.append(x);return b''
b=get('machina-data.json','https://lean.up.railway.app/api/data')
if b:
 d=json.loads(b);hits=[f for f in d['families'] if any(w in json.dumps(f).lower() for w in ['lcmgcd','alternating sums of motzkin','subtraction game'])];(p/'machina-hits.json').write_text(json.dumps({'commit':d.get('commit'),'generated_at':d.get('generated_at'),'hits':hits},indent=2));print(json.dumps(hits,indent=2)[:9000])
get('infinite-log.pdf','https://cfc.nankai.edu.cn/_upload/article/files/46/d2/6d0b34c14983adec423e3874b5bb/01f7c9ff-1074-479b-9cb0-a7eebcaf687c.pdf')
(p/'http.json').write_text(json.dumps(r,indent=2))
