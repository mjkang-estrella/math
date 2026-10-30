import pathlib,re,urllib.request,json,hashlib,datetime,subprocess
L=pathlib.Path(__file__).parent;t=(L/'survey-index.html').read_text();start=t.lower().index('on cliques corona')
url=re.search(r'href="([^"]+\.pdf)"',t[start:])[1]
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'route':'publisher volume index actual title link, not guessed blocked route'}
try:
 with urllib.request.urlopen(url,timeout=25) as f:
  b=f.read(2500000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(L/'survey.pdf').write_bytes(b)
 subprocess.run(['pdftotext','-layout',str(L/'survey.pdf'),str(L/'survey.txt')],check=True)
except Exception as e:r['error']=str(e)
(L/'survey-http.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
