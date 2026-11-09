import pathlib,json,hashlib,datetime,urllib.request,subprocess
O=pathlib.Path(__file__).resolve().parent;(O/'sources').mkdir(exist_ok=True);rs=[]
urls={'registry-head.json':'https://api.github.com/repos/openai/math/commits/HEAD','aim-algvision.html':'http://aimpl.org/algvision/1/','aim-charp.html':'http://aimpl.org/minimalmodcharp/3/','aim-braids.html':'http://aimpl.org/catheckehilbert/2/','hacon-xu.pdf':'https://arxiv.org/pdf/1302.0298v1','turner.pdf':'https://arxiv.org/pdf/2410.03068v1','boundaries.pdf':'https://arxiv.org/pdf/2610.38163v1','trifocal.pdf':'https://jmlr.csail.mit.edu/papers/volume19/17-436/17-436.pdf'}
for name,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=30) as q:
   data=q.read(30000000);r.update(status=q.status,final_url=q.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(O/'sources'/name).write_bytes(data)
  if name.endswith('.pdf'): subprocess.run(['pdftotext','-layout',str(O/'sources'/name),str(O/'sources'/name.replace('.pdf','.txt'))],check=True,timeout=20)
 except Exception as e:r['error']=str(e)
 rs.append(r);print(json.dumps(r),flush=True);(O/'sources/receipts.json').write_text(json.dumps(rs,indent=2)+'\n')
