import pathlib,json,urllib.request,urllib.error,datetime,hashlib,subprocess,re
O=pathlib.Path(__file__).resolve().parents[1];(O/'sources').mkdir(exist_ok=True);rows=json.loads((O/'statements.json').read_text());out=[];blocked=False
for row in rows:
 x=row['record'];aid=x['source_url'].split('/')[-1]
 if any(e['arxiv']==aid for e in out):continue
 url='https://arxiv.org/pdf/'+aid;e={'arxiv':aid,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'current PDF at retrieval; version label requires body inspection','read_level':'retained only; not automatically read'}
 if blocked:e['failure']='HOLD host parked after denial';out.append(e);continue
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research source reading (bounded)'}),timeout=9) as r:
   data=r.read(14000000);e['http_status']=r.status;e['final_url']=r.url
  assert data.startswith(b'%PDF'), 'not PDF'
  p=O/'sources'/f'{aid}.pdf';p.write_bytes(data);e.update(path=str(p.relative_to(O)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=8)
 except Exception as err:
  e['failure']=type(err).__name__+': '+str(err)
  if isinstance(err,urllib.error.HTTPError) and err.code in [403,429]:blocked=True
 out.append(e);print(aid,e.get('http_status'),e.get('failure','retained'),flush=True)
(O/'retained-sources.json').write_text(json.dumps(out,indent=2)+'\n')
