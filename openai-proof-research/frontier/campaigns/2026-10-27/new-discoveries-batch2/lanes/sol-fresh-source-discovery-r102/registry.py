from pathlib import Path
import json,urllib.request,urllib.parse,hashlib,datetime,re
P=Path(__file__).resolve().parent;R=next(x for x in P.parents if x.name=='openai-proof-research');log=json.loads((P/'http.json').read_text());terms=re.compile(r'quasi.?regulariz|Hoang|Mandrescu|Pereyra|domination.?polynomial|Alikhani|AutoGraphForge|Pastorek',re.I)
def get(n,u):
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read();s=r.status
  (P/'sources'/n).write_bytes(b);log.append(dict(url=u,status=s,file='sources/'+n,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));return b
 except Exception as e:log.append(dict(url=u,error=str(e)));return None
heads={k:json.loads((P/'sources'/f'{k}-head.json').read_text())['sha'] for k in ['omega','openai']};print(heads,flush=True)
base='556e7696bbabaff203d45456d177c5ce5b714212';h=heads['omega'];d=json.loads(get('omega-delta.json',f'https://api.github.com/repos/the-omega-institute/trureturing/compare/{base}...{h}'));print('delta',d.get('total_commits'),len(d.get('files',[])),flush=True)
hits=[]
for i,f in enumerate(d.get('files',[])):
 if f['status']=='removed':continue
 b=get(f'omega-delta-body-{i}.txt',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/'+urllib.parse.quote(f['filename']))
 if b and terms.search(b.decode(errors='replace')):hits.append(dict(file=f['filename'],local=f'sources/omega-delta-body-{i}.txt'))
# Fresh terms on inherited complete baseline and every cached delta body; no semantic absence assertion.
cache=[]
for lane in ['root-edge-irregulator-final-freeze-r1','sol-fresh-source-discovery-r99']:
 root=P.parent/lane
 for f in root.rglob('*'):
  if f.is_file() and f.suffix.lower() in ['.txt','.md','.json','.yaml','.lean']:
   b=f.read_bytes();s=b.decode(errors='replace')
   if terms.search(s):cache.append(dict(file=str(f.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),lines=[l[:1200] for l in s.splitlines() if terms.search(l)][:15]))
(P/'registry-screen.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),heads=heads,base=base,delta_commits=d.get('total_commits'),delta_files=len(d.get('files',[])),new_body_hits=hits,inherited_hits=cache,limit='Inherited older baseline/chain is not semantic clearance; exact fresh terms only. No historical global priority claim.'),indent=2));(P/'http.json').write_text(json.dumps(log,indent=2));print('hits',hits,len(cache))
