import pathlib,subprocess,hashlib,json,xml.etree.ElementTree as ET
L=pathlib.Path(__file__).resolve().parent
p=L/'retrieved/journal-pdf.frozen';a=hashlib.sha256(p.read_bytes()).hexdigest()
q=L/'retrieved/journal-text.body';subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True)
r=L/'retrieved/journal-text.frozen';r.write_bytes(q.read_bytes());assert q.read_bytes()==r.read_bytes();assert hashlib.sha256(p.read_bytes()).hexdigest()==a
(L/'extraction.json').write_text(json.dumps(dict(source_sha256=a,text_sha256=hashlib.sha256(r.read_bytes()).hexdigest(),tool='pdftotext -layout',original=str(q.relative_to(L)),copy=str(r.relative_to(L))),indent=2)+'\n')
for p in sorted((L/'frozen').glob('*-frozen/*.xml')):
 try:
  root=ET.fromstring(p.read_bytes());entries=root.findall('{http://www.w3.org/2005/Atom}entry');print(p.parent.name,[(e.findtext('{http://www.w3.org/2005/Atom}id'),e.findtext('{http://www.w3.org/2005/Atom}title')) for e in entries])
 except Exception as e:print(str(p),str(e))
for name in ['ledger.json','prior-campaign-context.json']:
 obj=json.loads((L/'administrative'/name).read_text()); print(name,'top keys',list(obj), 'renewal matches',[str(x)[:1500] for x in obj.values() if 'renewal' in str(x).lower()])
