import urllib.request,json,hashlib,datetime,pathlib
R=[]
def fetch(u,p):
 try:
  r=urllib.request.urlopen(u,timeout=20);b=r.read();pathlib.Path(p).write_bytes(b);R.append(dict(url=u,status=r.status,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));return b
 except Exception as e:R.append(dict(url=u,error=str(e)));return b''
heads=json.load(open('outputs/registries.json'))
repo='the-omega-institute/trureturing';head=heads[repo]['head'];b=fetch(f'https://api.github.com/repos/{repo}/git/trees/{head}','sources/omega-root.json')
if b:
 j=json.loads(b)
 for x in j.get('tree',[]):
  if x['path'] in ['D5','Problems']:
   fetch(f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1','sources/omega-'+x['path']+'.json')
for a in ['2502.02826','2207.10171','2209.08507','2210.00669','2210.00508','2210.11117']:
 fetch('https://arxiv.org/abs/'+a,'sources/'+a+'-abs.html')
fetch('https://arxiv.org/pdf/2110.12168','sources/2110.12168.pdf')
fetch('https://tesidottorato.depositolegale.it/bitstream/20.500.14242/212520/4/phdunige_5182815.pdf','sources/genova-thesis.pdf')
json.dump(R,open('outputs/prior-http.json','w'),indent=2)
