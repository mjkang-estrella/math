import pathlib,json,hashlib,urllib.request,datetime,subprocess
O=pathlib.Path(__file__).resolve().parent;log=json.loads((O/'source-provenance.json').read_text())
for a,v,issue in [('1961','2','16'),('1973','2','28'),('2040','3','29'),('1795','1','14')]:
 u=f'https://content.ems.press/assets/public/full-texts/serials/owr/5/{v}/{a}/online/10.4171-owr-2008-{issue}.pdf'
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as r:b=r.read()
  p=O/('ems'+a+'.pdf');p.write_bytes(b);e={'url':u,'version':'publisher report 2008','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'coverage':'PDF bytes bound before extraction'};log.append(e);(O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);b=t.read_bytes();log.append({'path':t.name,'derived_from':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'coverage':'derivative bound before content search'})
 except Exception as e:log.append({'url':u,'error':str(e),'retry':False})
 (O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
print('done')
