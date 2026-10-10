from pathlib import Path
import urllib.request,urllib.error,datetime,json,hashlib,subprocess
S=Path('frontier/sources/i82_measured_group_operator_discovery'); (S/'primary').mkdir(exist_ok=True)
urls=[('szabo-published.pdf','https://msp.org/apde/2025/18-6/apde-v18-n6-p02-p.pdf'),('szabo-page.html','https://arxiv.org/abs/2301.12846'),('banna-cebron.pdf','https://www.math.uni-sb.de/ag/speicher/banna/Operatorvaluedmatrices.pdf'),('banna-page.html','https://arxiv.org/abs/1811.05373'),('abert-weiss.pdf','https://arxiv.org/pdf/1103.1063v2'),('abert-page.html','https://arxiv.org/abs/1103.1063'),('bot.pdf','https://arxiv.org/pdf/1010.0565v1'),('bot-page.html','https://arxiv.org/abs/1010.0565')]
for name,url in urls:
 r={'url':url,'captured':datetime.datetime.now(datetime.timezone.utc).isoformat(),'local':str(S/'primary'/name)}
 try:
  with urllib.request.urlopen(url,timeout=45) as f:b=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
 except urllib.error.HTTPError as ex:b=ex.read();r.update(status=ex.code,error=str(ex))
 except Exception as ex:b=b'';r.update(error=str(ex))
 Path(r['local']).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 if b.startswith(b'%PDF'):
  p=subprocess.run(['pdftotext','-layout',r['local'],r['local']+'.txt'],capture_output=True);r['extraction']={'code':p.returncode,'stderr':p.stderr.decode(),'local':r['local']+'.txt','sha256':hashlib.sha256(Path(r['local']+'.txt').read_bytes()).hexdigest()}
 with (S/'primary-requests.jsonl').open('a') as f:f.write(json.dumps(r,sort_keys=True)+'\n')
 print(name,r.get('status'),len(b),flush=True)
