import pathlib,json,urllib.request,hashlib,datetime
L=pathlib.Path(__file__).parent;out=[]
for name,u in [('384542-successor-v1','https://arxiv.org/pdf/2403.08925v1'),('384373-successor','https://math.bnu.edu.cn/docs/20150624161407552012.pdf')]:
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'discovery':'public search result; not a clearance'}
 try:
  with urllib.request.urlopen(u,timeout=35) as f:b=f.read(8000000);r.update(final_url=f.url,headers=dict(f.headers),status=f.status)
  assert len(b)<8000000;p=L/'evidence'/(name+'.pdf');p.write_bytes(b);r.update(file=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as e:r['error']=repr(e)
 out.append(r);(L/'successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(r.get('file',r.get('error')))
