import pathlib,json,re,hashlib,urllib.request,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
for r in json.loads((D/'reservation.json').read_text())['rows']:
 a=r['source_url'].split('/')[-1];s=(D/'sources'/f'{a}.abs').read_text();title=re.search(r'<title>(.*?)</title>',s,re.S);versions=re.findall(r'/abs/'+re.escape(a)+r'v\d+',s)
 print(r['mathdb_id'],title.group(1) if title else '', sorted(set(versions)))
for name in ['openai-head','omega-head']:
 o=json.loads((D/'sources'/name).read_text());print(name,o['sha'])
urls={'rowmotion-correct':'https://arxiv.org/pdf/2311.07133','thomas-claim':'https://celebratio.org/Haken_W/article/795/','book-domains':'https://micro.econ.kit.edu/downloads/CondorcetDomains_Buch_Puppe_Slinko.pdf'}
r=[]
for name,url in urls.items():
 o={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=18) as f:b=f.read();o['status']=f.status
  p=D/'sources'/name;p.write_bytes(b);o.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],capture_output=True,timeout=18)
 except Exception as e:o['error']=str(e)
 r.append(o);print(o,flush=True)
(D/'sources/audit-receipts.json').write_text(json.dumps(r,indent=2)+'\n')
