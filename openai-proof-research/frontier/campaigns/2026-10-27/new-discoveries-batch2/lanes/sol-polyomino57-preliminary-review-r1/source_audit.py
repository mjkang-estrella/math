import pathlib,urllib.request,datetime,hashlib,json,re
L=pathlib.Path(__file__).resolve().parent
(L/'sources').mkdir(exist_ok=True);logs=[]
for name,url in [('omega','https://github.com/the-omega-institute/trureturing'),('openai','https://github.com/openai/math'),('aim','https://github.com/MColbrook/AIM'),('count','https://github.com/suvrit/count-ex-machina')]:
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as r:data=r.read(3000000);row['status']=r.status
  (L/'sources'/f'{name}-root.html').write_bytes(data)
  row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),oids=sorted(set(re.findall(r'"currentOid":"([a-f0-9]{40})"',data.decode()))))
 except Exception as e:row['error']=str(e)
 logs.append(row)
(L/'http-receipt.json').write_text(json.dumps(logs,indent=2));print(json.dumps(logs,indent=2))
# Inspect every frozen report/log and source artifact; actual mathematical code also read separately.
rows=[]
for p in sorted((L/'input').rglob('*')):
 if p.is_file() and p.name!='embedding-certificate.jsonl':
  s=p.read_text();rows.append({'path':str(p.relative_to(L)),'characters':len(s),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(L/'read-inventory.json').write_text(json.dumps(rows,indent=2))
for f in ['checks.json','independent-checks.json','certificate-audit.json','registry-cache-screen.json']:
 d=json.loads((L/'input'/f).read_text());print(f, type(d).__name__)
