import pathlib,urllib.request,json,datetime,hashlib,re,sys
from html.parser import HTMLParser
b=pathlib.Path(__file__).resolve().parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,d):self.out.append(d)
urls={'lee-v2':'https://arxiv.org/html/2602.02450v2','rather-v1':'https://arxiv.org/html/2606.04789v1','pereyra-v1':'https://arxiv.org/html/2605.14076v1'}
if len(sys.argv)>1:urls=json.loads(sys.argv[1])
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f: data=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  (b/'sources'/name).write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
  if data.lstrip().startswith(b'<'):
   p=Text();p.feed(data.decode());(b/'sources'/(name+'.txt')).write_text('\n'.join(p.out))
 except Exception as e:r['error']=str(e)
 with (b/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(name,r.get('status'),r.get('error'))
