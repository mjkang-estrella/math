from pathlib import Path
import requests,hashlib,json,datetime,sys,subprocess
L=Path(__file__).parent
def get(name,url):
 p=L/'primary'/name
 try:
  r=requests.get(url,timeout=24,headers={'User-Agent':'Research source verification (bounded single retrieval)'})
  p.write_bytes(r.content)
  rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':r.status_code,'path':str(p),'sha256':hashlib.sha256(r.content).hexdigest(),'bytes':len(r.content)}
  with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  if r.status_code in (403,429) or any(w in r.text[:3000].lower() for w in ['captcha','verify you are human']):print('STOP',name,r.status_code);return
  if r.content.startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  else:
   import re,html
   p.with_suffix('.txt').write_text(html.unescape(re.sub('<[^>]+>',' ',r.text)))
  print(name,r.status_code,len(r.content))
 except Exception as e:
  with (L/'failures.jsonl').open('a') as f:f.write(json.dumps({'url':url,'error':repr(e)})+'\n')
  print(name,repr(e))
if __name__=='__main__':
 for name,url in json.loads(sys.argv[1]):get(name,url)
