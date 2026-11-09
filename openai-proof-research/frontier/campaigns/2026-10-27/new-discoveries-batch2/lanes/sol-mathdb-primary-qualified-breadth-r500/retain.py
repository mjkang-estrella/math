import pathlib,urllib.request,urllib.error,hashlib,json,datetime,subprocess
O=pathlib.Path(__file__).resolve().parent; S=O/'sources';S.mkdir(exist_ok=True); records=[]
for a in ['2203.14842','2204.06101','2204.07638','2204.12012','2204.09884','2205.05530','2206.15307','2207.02271','2207.03941','2208.08506','2208.12209','2209.08946','2209.09221']:
 url='https://arxiv.org/pdf/'+a;r={'url':url,'retrieved_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=12) as response:
   data=response.read(12000000);r['final_url']=response.url;r['headers']=dict(response.headers)
  p=S/(a+'.pdf');p.write_bytes(data);r.update(pdf=str(p.relative_to(O)),pdf_sha256=hashlib.sha256(data).hexdigest(),pdf_size=len(data))
  if not data.startswith(b'%PDF'):r['failure']='not PDF; stop';records.append(r);break
  t=S/(a+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);b=t.read_bytes();r.update(text=str(t.relative_to(O)),text_sha256=hashlib.sha256(b).hexdigest(),text_size=len(b),status='retained_bound_before_search')
 except Exception as e:
  r.update(status='failure',failure=repr(e));records.append(r);print(a,r['failure'],flush=True)
  if isinstance(e,urllib.error.HTTPError) and e.code in [403,429]:break
  continue
 records.append(r);print(a,r['status'],flush=True)
 (O/'source-provenance.json').write_text(json.dumps(records,indent=2)+'\n')
(O/'source-provenance.json').write_text(json.dumps(records,indent=2)+'\n')
