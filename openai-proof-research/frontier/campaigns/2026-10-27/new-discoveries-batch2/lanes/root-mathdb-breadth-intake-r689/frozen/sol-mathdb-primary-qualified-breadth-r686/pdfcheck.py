import pathlib,json,re,urllib.request,datetime,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parent;out=json.loads((L/'source-provenance.json').read_text())
for id in [404190,404218,404497]:
 h=(L/f'{id}.html').read_text(); url=re.search(r'https://content.ems.press/assets/public/full-texts/[^"\\]+\.pdf',h).group()
 r={'id':id,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'kind':'primary report PDF'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as f:b=f.read(15000000);r['status']=f.status
  p=L/f'{id}.pdf';p.write_bytes(b);r.update(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest());out.append(r);(L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(L/f'{id}.txt')],check=True)
  p=L/f'{id}.txt';b=p.read_bytes();out.append({'id':id,'kind':'bound text derivative before search','path':p.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()});(L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  for x in json.loads((L/'literal-records.json').read_text()):
   if x['record']['mathdb_id']==id:print(id,x['record']['source_name'])
 except Exception as e:r['failure']=str(e);out.append(r);(L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(str(e))
