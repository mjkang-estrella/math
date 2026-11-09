import pathlib,json,urllib.request,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1];head='1764a0c7f33be6acf6dcaf4ad4007da021469ae9';rec=[]
def get(name,url):
 try:
  with urllib.request.urlopen(url,timeout=20) as h:b=h.read()
  (L/('sources/'+name)).write_bytes(b);rec.append(dict(url=url,status=200,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));return b
 except Exception as e:rec.append(dict(url=url,error=str(e)));return None
b=get('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+head)
if b:
 for x in json.loads(b)['tree']:
  if x['path'] in ['D5','Problems']:get('omega-'+x['path']+'.json',x['url']+'?recursive=1')
for path in ['D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.lean','Blueprint/D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.md']:
 get('public-'+path.rsplit('/',1)[1],'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+path)
get('trees-prior-actual.pdf','https://arxiv.org/pdf/2507.17913')
(L/'outputs/registry-scopes-http.json').write_text(json.dumps(rec,indent=2));print(json.dumps(rec))
