import pathlib,json,re,hashlib,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent;B=L.parent
s=(L/'fetch_sources.py').read_text().split('items=[]')[0];g={'__file__':str(L/'fetch_sources.py')};exec(compile(s,str(L/'fetch_sources.py'),'exec'),g)
jobs=[(x+'-head.html','https://github.com/'+r+'/commits/HEAD') for x,r in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]]
jobs.extend([('gessel-proof.pdf','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v23i3p15/pdf'),('aluffi-refutation.pdf','https://arxiv.org/pdf/2005.02673'),('lobb-grant.pdf','https://arxiv.org/pdf/1212.4511')])
for f in sorted((B/'expanded-corpus-r254').glob('pool-index-*.receipt.json')):
 r=json.loads(f.read_text());jobs.append((f.stem.replace('.receipt','')+'.raw',r['url']))
with g['concurrent'].futures.ThreadPoolExecutor(max_workers=2) as e:list(e.map(g['fetch'],jobs))
pat=re.compile(r'Swanepoel|collapsing|Pirates|Treasure|monotone.triangle|Riegler|tolerance|cocomparability|matching.complex|Jonsson|Gessel|Zentner|Lobb|Chan.Robbins|thick.building|separated.graph|Friedrichs|Aluffi',re.I)
paths=[B/'expanded-corpus-r254/openai-complete-preprints.body',B/'expanded-corpus-r254/pool-tree.body',B/'path-polynomial-source-qualification-r1/omega-current-D5.body',B/'path-polynomial-source-qualification-r1/omega-current-Blueprint.body',L/'sources/leanpool-projects.yml']+list((L/'sources').glob('pool-index-*.raw'))
out=[]
for p in paths:
 if not p.exists():out.append({'path':str(p),'missing':True});continue
 data=p.read_bytes();o={'path':str(p),'sha256':hashlib.sha256(data).hexdigest()}
 try:
  d=json.loads(data);o.update(truncated=d.get('truncated'),tree=d.get('sha'));o['matches']=[x for x in d.get('tree',[]) if pat.search(x['path'])]
 except Exception:o['matches']=[{'line':i,'text':x[:1000]} for i,x in enumerate(data.decode(errors='replace').splitlines(),1) if pat.search(x)]
 out.append(o)
(L/'registry-screen.json').write_text(json.dumps(out,indent=2))
for x in ['openai','omega','pool']:
 p=L/'sources'/f'{x}-head.html'
 if p.exists():print(x,re.findall(r'"oid":"([0-9a-f]{40})"',p.read_text())[:1])
print('matches',[(o['path'],len(o.get('matches',[]))) for o in out])
