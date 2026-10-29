import pathlib,json,gzip,re,urllib.request,datetime,hashlib
L=pathlib.Path(__file__).resolve().parent;B=L.parent
hits=[]
for repo in ['omega','openai']:
 p=B/'root-edge-irregulator-current-prior-r1'/(repo+'-tree.txt.gz')
 for line in gzip.open(p,'rt'):
  if re.search('narayana|fuss|amazing|signless.*spread|spread.*signless',line,re.I):hits.append({'repo':repo,'path':line.strip()})
(L/'registry-hits.json').write_text(json.dumps(hits,indent=2));print(json.dumps(hits,indent=2))
log=json.loads((L/'http.json').read_text());heads={}
for n,repo,base in [('omega','the-omega-institute/trureturing','a6f8ee6614e0faf9dfa2cce46d1eb758dea97c335'),('openai','openai/math','7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a')]:
 for name,url in [(n+'-head.json',f'https://api.github.com/repos/{repo}/commits/HEAD')]:
  row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=30) as f:b=f.read(2000000);row.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
   (L/'sources'/name).write_bytes(b);h=json.loads(b)['sha'];heads[n]=h
  except Exception as e:row['error']=str(e);h=None
  log.append(row)
 if h and h!=base:
  u=f'https://api.github.com/repos/{repo}/compare/{base}...{h}';row={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(u,timeout=30) as f:b=f.read(12000000);row.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
   (L/'sources'/(n+'-delta.json')).write_bytes(b);d=json.loads(b);print(n,'delta',len(d.get('files',[])),d.get('total_commits'))
  except Exception as e:row['error']=str(e)
  log.append(row)
(L/'heads.json').write_text(json.dumps(heads,indent=2));(L/'http.json').write_text(json.dumps(log,indent=2))
