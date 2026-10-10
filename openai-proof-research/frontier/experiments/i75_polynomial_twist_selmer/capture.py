import pathlib,json,urllib.request,hashlib,datetime,subprocess,concurrent.futures,re
S=pathlib.Path('frontier/sources/i75_polynomial_twist_selmer'); P=S/'primary';P.mkdir(exist_ok=True)
items=[('ks','https://arxiv.org/abs/2606.31649'),('smith','https://arxiv.org/abs/2503.17619'),('smith-I','https://arxiv.org/abs/2207.05674'),('smith-II','https://arxiv.org/abs/2207.05143'),('kps','https://arxiv.org/abs/2409.02080'),('field-change','https://arxiv.org/abs/2206.13403')]
def fetch(name,url,ext):
 start=datetime.datetime.now(datetime.timezone.utc).isoformat();p=P/(name+ext);r={'name':name,'url':url,'started':start,'path':str(p)}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I75 mathematical source audit'}),timeout=50) as f:
   data=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers.items()))
  p.write_bytes(data);r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if ext=='.pdf':
   z=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True);r.update(extraction_exit=z.returncode,extraction_stderr=z.stderr.decode());(P/(name+'.txt')).write_bytes(z.stdout)
 except Exception as e:r['error']=repr(e)
 return r
records=list(concurrent.futures.ThreadPoolExecutor(6).map(lambda x:fetch(*x,'.html'),items))
versions={}
for name,url in items:
 t=(P/(name+'.html')).read_text();v=re.findall(r'\[v(\d+)\]',t);versions[name]={'url':url,'versions':v,'latest':max(map(int,v)) if v else None}
req=[]
for name in ['smith-I','smith-II','kps','field-change']:
 aid=dict(items)[name].rsplit('/',1)[1];req.append((name,'https://arxiv.org/pdf/'+aid+'v'+str(versions[name]['latest']),'.pdf'))
req.append(('zhang','https://zhangshenxing.github.io/publications/Zhang2025.pdf','.pdf'))
records+=list(concurrent.futures.ThreadPoolExecutor(5).map(lambda x:fetch(*x),req))
(S/'requests.json').write_text(json.dumps(records,indent=2)+'\n');(S/'versions.json').write_text(json.dumps(versions,indent=2)+'\n')
print(json.dumps({'versions':versions,'requests':[{k:v for k,v in r.items() if k in ['name','status','error','bytes']} for r in records]},indent=2))
