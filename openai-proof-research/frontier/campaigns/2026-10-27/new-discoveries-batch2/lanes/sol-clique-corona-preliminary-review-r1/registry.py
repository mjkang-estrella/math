import pathlib,json,hashlib,gzip,re,urllib.request,datetime
L=pathlib.Path(__file__).parent;root=L.parents[6]
records=json.loads((L/'copies/registry-screen.json').read_text())['records'];out=[]
for i,r in enumerate(records):
 p=pathlib.Path(r['path'])
 if not p.is_absolute():p=pathlib.Path('/home/mj-kang/Documents/Dev/math')/p
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'];q=L/'registry-copies'/str(i);q.parent.mkdir(exist_ok=True);q.write_bytes(b)
 text=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
 hits=[line[:1000] for line in text.splitlines() if re.search(r'corona|well.cover|mandrescu|hoang|levit|independence.polynomial|cliquecorona',line,re.I)]
 out.append({'original':str(p),'copy':str(q),'sha256':r['sha256'],'bytes':len(b),'hits':hits})
print(json.dumps([{k:v for k,v in r.items() if k not in ['hits']}|{'hits':r['hits'][:8],'hit_count':len(r['hits'])} for r in out],indent=2))
(L/'registry-copy-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
url='https://api.github.com/repos/the-omega-institute/trureturing/compare/d36a58e865e46580f127ef7a09d64ccbc2370296...2b143c68ca72fcaccfe71d6233cb2c6db4c8c059'
r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=25) as f:
  b=f.read(3000000);(L/'omega-fixed-delta.json').write_bytes(b);d=json.loads(b);paths=[x['filename'] for x in d.get('files',[])];r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),files=len(paths),commits=d.get('total_commits'),paths=paths,capped=len(paths)>=300)
except Exception as e:r['error']=str(e)
(L/'registry-current-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
