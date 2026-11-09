import pathlib,urllib.request,urllib.error,urllib.parse,hashlib,json,datetime,sys,time,re,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
denied=set(json.loads((D/'sources/denied.json').read_text()) if (D/'sources/denied.json').exists() else [])
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Redirect)
def fetch(url,name):
 host=urllib.parse.urlparse(url).hostname; r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if host in denied:r['status']='skipped denied host';return r
 try:
  with op.open(urllib.request.Request(url,headers={'User-Agent':'MathematicsResearch/1.0'}),timeout=20) as f:b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest());(D/'sources'/name).write_bytes(b)
 except urllib.error.HTTPError as e:
  r['status']=e.code
  if e.code in [403,429]:denied.add(host)
 except Exception as e:r['status']=str(e)
 (D/'sources/denied.json').write_text(json.dumps(sorted(denied)))
 (D/'sources'/(name+'.receipt.json')).write_text(json.dumps(r,indent=2));return r
if __name__=='__main__':
 if sys.argv[1]=='papers':
  rows=json.loads((D/'reservation.json').read_text())['rows']
  for r in rows[int(sys.argv[2]):int(sys.argv[3])]:
   a=r['source_url'].rsplit('/',1)[1];print(fetch(r['source_url'],a+'.html'),flush=True)
   p=D/'sources'/ (a+'.html');vs=sorted(set(re.findall(a+r'v(\d+)',p.read_text()))) if p.exists() else []
   for v in vs or ['1']:
    name=a+'v'+v+'.pdf';print(fetch('https://arxiv.org/pdf/'+a+'v'+v,name),flush=True)
    if (D/'sources'/name).exists():subprocess.run(['pdftotext','-layout',str(D/'sources'/name),str(D/'sources'/(name+'.txt'))])
 else:print(fetch(sys.argv[1],sys.argv[2]))
