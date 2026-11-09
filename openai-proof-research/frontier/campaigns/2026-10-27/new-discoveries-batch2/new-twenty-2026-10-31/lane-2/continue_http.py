import requests,pathlib,hashlib,json,datetime,subprocess
p=pathlib.Path('.')
log=json.load(open('http-manifest.json'))
def get(k,u):
 r=requests.get(u,timeout=40); ext='pdf' if r.content.startswith(b'%PDF') else 'txt'; f=p/(k+'.'+ext);f.write_bytes(r.content)
 if ext=='pdf':subprocess.run(['pdftotext','-layout',str(f),str(p/(k+'.txt'))],check=True)
 log.append(dict(name=k,url=u,status=r.status_code,file=str(f),sha256=hashlib.sha256(r.content).hexdigest(),date=datetime.datetime.now(datetime.timezone.utc).isoformat(),headers=dict(r.headers)))
 (p/'http-manifest.json').write_text(json.dumps(log,indent=2));return r
head=json.load(open('registry-head.txt'))['sha']
r=get('registry-root','https://api.github.com/repos/openai/math/git/trees/'+head)
pre=next(x['sha'] for x in r.json()['tree'] if x['path']=='preprints')
r=get('registry-preprints','https://api.github.com/repos/openai/math/git/trees/'+pre+'?recursive=1');print('preprints truncated',r.json().get('truncated'))
get('registry-pinned-contents','https://raw.githubusercontent.com/openai/math/'+head+'/CONTENTS.md')
get('janson','https://www2.math.uu.se/~svantejs/papers/sj280.pdf')
rows=json.load(open('../../lanes/sol-mathdb-primary-qualified-breadth-r728/literal-records.json'))
for x in rows:
 r=x['record']; i=r['mathdb_id']
 if i in [319825,320868,321049]:get('mathdb-'+str(i),r['canonical_url'])
