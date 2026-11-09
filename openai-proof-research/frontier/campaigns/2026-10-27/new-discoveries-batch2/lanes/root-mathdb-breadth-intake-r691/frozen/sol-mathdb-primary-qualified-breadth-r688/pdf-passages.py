import urllib.request,json,pathlib,hashlib,datetime,subprocess
O=pathlib.Path(__file__).resolve().parent;log=json.loads((O/'source-provenance.json').read_text());der=[]
for name,file,pages in [('permutations',48646,[9,11,12,13,14,15,16,17]),('cayley',52253,[23]),('designs',52246,[21,62])]:
 url=f'https://ems.press/content/serial-article-files/{file}?nt=1';p=O/(name+'.pdf')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as r:b=r.read(8000000);final=r.url
  p.write_bytes(b);e={'path':p.name,'url':url,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'status':200};log.append(e);(O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  for page in pages:
   out=O/f'{name}-p{page}.txt';subprocess.run(['pdftotext','-f',str(page),'-l',str(page),'-layout',str(p),str(out)],check=True)
   bb=out.read_bytes();der.append({'path':out.name,'parent':p.name,'pdf_page':page,'sha256':hashlib.sha256(bb).hexdigest(),'size':len(bb)})
   (O/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
  print(name,'bound PDF and page derivatives',pages)
 except Exception as ex:log.append({'url':url,'failure':str(ex)});(O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(log[-1])
