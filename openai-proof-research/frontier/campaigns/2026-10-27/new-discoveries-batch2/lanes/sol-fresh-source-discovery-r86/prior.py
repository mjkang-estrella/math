import pathlib,json,gzip,re,urllib.request,datetime,hashlib,subprocess
P=pathlib.Path(__file__).resolve().parent; B=P.parents[0]; root=P.parents[5]
log=json.loads((P/'http.json').read_text())
heads={n:json.loads((P/'sources'/(n+'-head.json')).read_text())['sha'] for n in ['omega','openai']}
(P/'heads.json').write_text(json.dumps(heads,indent=2));print(heads)
def get(n,u):
 row={'name':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=30) as f:b=f.read(18000000);row.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(P/'sources'/n).write_bytes(b)
 except Exception as e:row['error']=str(e);b=None
 log.append(row);return b
b=get('boyd.pdf','https://web.stanford.edu/~boyd/cvxbook/bv_cvxslides.pdf')
if b:subprocess.run(['pdftotext','-layout',str(P/'sources/boyd.pdf'),str(P/'sources/boyd.pdf.txt')],check=True)
for n,repo,base in [('omega','the-omega-institute/trureturing','23a4ae6f843d1635869b7656fb6bd681121447a8'),('openai','openai/math','7ef5c0cc')]:
 if n=='openai':
  # full cached head evidence specifies the base, avoiding guessed short revisions
  z=json.loads((B/'sol-fresh-source-discovery-r84/sources/openai-head').read_text());base=z['sha']
 if base!=heads[n]:get(n+'-delta.json',f'https://api.github.com/repos/{repo}/compare/{base}...{heads[n]}')
lines=[]
cache=B/'root-edge-irregulator-current-prior-r1'
for n in ['omega','openai']:
 for line in gzip.open(cache/(n+'-tree.txt.gz'),'rt'):
  if re.search('eruguz|returns|benford|fragment|hyman|unimodal|concav',line,re.I):lines.append({'repo':n,'path':line.strip()})
(P/'registry-path-hits.json').write_text(json.dumps(lines,indent=2));print('path hits',len(lines));print(json.dumps(lines[:25],indent=2))
(P/'http.json').write_text(json.dumps(log,indent=2))
