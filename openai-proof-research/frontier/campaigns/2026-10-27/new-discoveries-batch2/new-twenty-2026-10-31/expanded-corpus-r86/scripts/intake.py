import pathlib,json,hashlib,subprocess,re,datetime,urllib.request,urllib.error
L=pathlib.Path(__file__).resolve().parents[1]; B=L.parents[1]; R=L.parents[6]
def sha(x):return hashlib.sha256(x).hexdigest()
receipts=json.loads((L/'outputs/http-receipts.json').read_text()) if (L/'outputs/http-receipts.json').exists() else []
def fetch(url,name):
 p=L/'sources'/name
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-r86'}),timeout=25) as r:data=r.read();status=r.status
 except urllib.error.HTTPError as e:data=e.read();status=e.code
 except Exception as e:data=str(e).encode();status='error'
 p.write_bytes(data);receipts.append({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'status':status,'file':str(p.relative_to(L)),'sha256':sha(data),'bytes':len(data)});(L/'outputs/http-receipts.json').write_text(json.dumps(receipts,indent=2)); print(name,status,len(data),flush=True)
 return status
if __name__=='__main__':
 for repo,name in [('openai/math','registry-openai-head.json'),('the-omega-institute/trureturing','registry-omega-head.json')]:fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',name)
 for i in [348288,349631,350871,351203,354079,356575,348638]:
  d=json.loads((L/f'sources/{i}.jsonl').read_text());a=d['source_url'].split('/')[-1]
  if fetch('https://arxiv.org/pdf/'+a,f'{i}.pdf')==200:
   subprocess.run(['pdftotext','-layout',str(L/f'sources/{i}.pdf'),str(L/f'sources/{i}.txt')],check=True)
