from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent;D=L/'http';jobs=[];out={}
pat=re.compile(r'colorful|outerplanar|bichrom|J170|DifferenceSets|OddGraph|Kneser|InducedForest|Clifford|Amicab|WellSupported|PascalRhombus|Narayana|Dendrimer|EccentricityEntropy|GraphEntropy|StressFree|Toroidal|AbelianSquare|Blondeau|Pauli',re.I)
for name,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 h=json.loads((D/(name+'-head.json')).read_text())['sha'];allx={}
 for p in list(D.glob(name+'-complete-*.json'))+[D/(name+'-tree.json')]:
  t=json.loads(p.read_text());print(p.name,'truncated',t.get('truncated'),len(t.get('tree',[])))
  prefix='' if p.name.endswith('-tree.json') else p.name.split('-complete-')[1][:-5].replace('_','/')+'/'
  for x in t.get('tree',[]):allx[prefix+x['path']]={**x,'path':prefix+x['path']}
 matches=[x for x in allx.values() if pat.search(x['path'])];out[name]=matches;print(name,'matches', '\n'.join(x['path'] for x in matches)[:5000])
 if name=='openai':
  root=json.loads((D/'openai-root-complete.json').read_text())
  for x in root.get('tree',[]):
   if x['path']=='preprints':jobs.append(['openai-preprints-full.json',f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1'])
 for x in matches:
  if x['type']=='blob' and re.search(r'\.(lean|md|tex|json)$',x['path']) and x.get('size',0)<300000:jobs.append([name+'-matched-'+hashlib.sha256(x['path'].encode()).hexdigest()[:12]+Path(x['path']).suffix,f'https://raw.githubusercontent.com/{repo}/{h}/{x["path"]}'])
 if name=='omega':
  for p in ['D5/S1/Words','D5/S2/Graphs','D5/S3/Graphs','D5/S1/Graph','D5/S2/Graph','D5/S1/Combinatorics']:
   if p in allx:jobs.append(['omega-specific-'+p.replace('/','_')+'.json',f'https://api.github.com/repos/{repo}/git/trees/{allx[p]["sha"]}?recursive=1'])
(L/'deep-screen.json').write_text(json.dumps(out,indent=2));(L/'deep-plan.json').write_text(json.dumps(jobs));print('jobs',len(jobs))
