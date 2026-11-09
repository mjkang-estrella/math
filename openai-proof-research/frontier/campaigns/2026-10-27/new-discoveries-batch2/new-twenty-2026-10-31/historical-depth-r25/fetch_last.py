import pathlib,json,hashlib,datetime,urllib.request,subprocess
O=pathlib.Path(__file__).resolve().parent;(O/'sources').mkdir(exist_ok=True);rs=[]
urls={'kileel.pdf':'https://arxiv.org/pdf/1611.05947v1','omega-tree.json':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/9a0eb771556a6923c4bb4172f17c0ced963310eb?recursive=1'}
for name,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=30) as q:
   data=q.read(30000000);r.update(status=q.status,final_url=q.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(O/'sources'/name).write_bytes(data)
  if name.endswith('.pdf'): subprocess.run(['pdftotext','-layout',str(O/'sources'/name),str(O/'sources'/name.replace('.pdf','.txt'))],check=True,timeout=20)
 except Exception as e:r['error']=str(e)
 rs.append(r);print(json.dumps(r),flush=True);(O/'sources/last-receipts.json').write_text(json.dumps(rs,indent=2)+'\n')
