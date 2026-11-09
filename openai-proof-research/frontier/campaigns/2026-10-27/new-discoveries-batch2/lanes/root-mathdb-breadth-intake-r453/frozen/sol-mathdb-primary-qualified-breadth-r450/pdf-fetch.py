import pathlib,json,re,urllib.request,urllib.error,datetime,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parent;log=[];blocked=False
for p in sorted((L/'sources').glob('*.html')):
 urls=re.findall(r'https://content.ems.press/[^"<>\\ ]+\.pdf',p.read_text());urls=list(dict.fromkeys(urls))
 if not urls:log.append({'html':p.name,'status':'no advertised PDF'});continue
 u=urls[0];entry={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'parent':p.name}
 if blocked:entry['status']='HOLD host stopped';log.append(entry);continue
 try:
  with urllib.request.urlopen(u,timeout=15) as r:b=r.read(12000000);entry['status']=r.status
  assert b.startswith(b'%PDF')
  dest=p.with_suffix('.pdf');dest.write_bytes(b);entry.update(file=str(dest.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  q=subprocess.run(['pdftotext','-layout',str(dest),str(dest.with_suffix('.txt'))],capture_output=True,text=True);entry['extraction_exit']=q.returncode
 except Exception as e:
  entry.update(status='HOLD',error=str(e))
  if isinstance(e,urllib.error.HTTPError) and e.code in [403,429]:blocked=True
 log.append(entry);print(entry,flush=True)
(L/'pdf-access.json').write_text(json.dumps(log,indent=2)+'\n')
