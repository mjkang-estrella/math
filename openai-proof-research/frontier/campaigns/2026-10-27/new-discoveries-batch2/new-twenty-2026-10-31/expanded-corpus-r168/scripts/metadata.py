import pathlib,json,urllib.request,hashlib,datetime,re
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for i,o in json.loads((D/'extracted.json').read_text()).items():
 u=o['source_url'];r={'id':i,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=10) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest());(D/'sources'/i/'abs.html').write_bytes(b)
  s=b.decode();r['versions']=re.findall(r'\[v\d+\].{0,180}',s);r['title']=re.findall(r'<meta name="citation_title" content="(.*?)"',s);r['authors']=re.findall(r'<meta name="citation_author" content="(.*?)"',s)
 except Exception as e:r['error']=str(e)
 out.append(r);(D/'outputs/metadata.json').write_text(json.dumps(out,indent=2));print(i,r.get('versions',r.get('error')),flush=True)
