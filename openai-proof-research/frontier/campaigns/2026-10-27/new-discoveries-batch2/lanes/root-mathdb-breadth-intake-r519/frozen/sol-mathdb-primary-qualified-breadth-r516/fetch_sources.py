import pathlib,json,hashlib,urllib.request,datetime,subprocess
O=pathlib.Path(__file__).resolve().parent; L=O.parent
items=__import__('sys').argv[1:] or ['2308.07194','2308.10977','2310.06464','2312.09916','2310.09128']
prov=json.loads((O/'source-provenance.json').read_text()) if (O/'source-provenance.json').exists() else []
def stamp(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
for aid in items:
 # Reuse only a precisely matching immutable filename, never copy historical trees.
 cached=list(L.glob('*/'+aid+'.pdf'))
 e={'arxiv_id':aid,'requested_url':'https://arxiv.org/pdf/'+aid,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if cached:p=cached[0];e['acquisition']='existing_snapshot'
  else:
   p=O/(aid+'.pdf');req=urllib.request.Request(e['requested_url'],headers={'User-Agent':'bounded-research/1.0'})
   with urllib.request.urlopen(req,timeout=25) as res:
    e['response_url']=res.url;e['headers']=dict(res.headers);data=res.read(15000000)
   assert data.startswith(b'%PDF');p.write_bytes(data);e['acquisition']='public_primary_fetch'
  e['pdf']=stamp(p);prov.append(e);(O/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
  t=O/(aid+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=30)
  e['text']=stamp(t);e['body_coverage']='unread; binding only';(O/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
  print(aid,'BOUND',e['pdf']['sha256'],e['text']['size'])
 except Exception as ex:
  e['failure']=str(ex)
  if e not in prov:prov.append(e)
  (O/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n');print(aid,'FAIL',str(ex))
