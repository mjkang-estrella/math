exec(open(__file__.replace('registry.py','fetch.py')).read().split('jobs=')[0])
def get(k,u):
 r=requests.get(u,timeout=25);data=r.content;(o/(k+'.bin')).write_bytes(data);(o/(k+'.receipt.json')).write_text(json.dumps(dict(url=u,status=r.status_code,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(data).hexdigest()),indent=2));return r.json() if r.status_code==200 else {}
h=json.loads((o/'omega-head.bin').read_text())['sha'];root=get('omega-root',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')
res={}
for name in ['D5','Problems']:
 row=next(x for x in root['tree'] if x['path']==name);old=json.loads((o.parent.parent/'expanded-corpus-r56/sources'/('omega-'+name+'.bin')).read_text());res[name]=dict(tree=row['sha'],cached_tree=old['sha'],unchanged=row['sha']==old['sha'],truncated=old.get('truncated'),entries=len(old['tree']),cache_sha256=hashlib.sha256((o.parent.parent/'expanded-corpus-r56/sources'/('omega-'+name+'.bin')).read_bytes()).hexdigest(),hits=[x['path'] for x in old['tree'] if any(t in x['path'].lower() for t in ['redundant','steane','pandigital','domino','362436','362542','362895'])])
(o.parent/'registry-screen.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
for a in ['1709.03974']:
 u='https://arxiv.org/pdf/'+a;r=requests.get(u,timeout=25);(o/(a+'.bin')).write_bytes(r.content);(o/(a+'.receipt.json')).write_text(json.dumps(dict(url=u,status=r.status_code,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(r.content).hexdigest()),indent=2))
 if r.status_code==200:subprocess.run(['pdftotext','-layout',str(o/(a+'.bin')),str(o/(a+'.txt'))],timeout=10)
