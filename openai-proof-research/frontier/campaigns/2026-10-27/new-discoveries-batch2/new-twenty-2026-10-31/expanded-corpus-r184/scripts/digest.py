import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
hist=[]
for l in (D/'history-matches.txt').read_text().splitlines():
 if len(l)<2200 and not any(x in l for x in ['TASK.txt','coverage','alias-results','registry','context','reservation','routing','intake','inventory']):hist.append(l)
(D/'outputs/history-digest.txt').write_text('\n'.join(hist))
R=json.loads((D/'outputs/registry-screen.json').read_text());rows=json.loads((D/'reservation.json').read_text())['rows'];R['keyword_screens']={}
for row in rows:
 a=row['source_url'].split('/')[-1];patterns=[str(row['mathdb_id']),a]+re.findall(r'[A-Za-z]{5,}',row['title'])
 hits=[]
 for p in (D/'sources').glob('pool-*'):
  if p.suffix not in ['.yml','.jsonl','.txt','.md']:continue
  for i,l in enumerate(p.read_text().splitlines(),1):
   found=[w for w in patterns if w.lower() in l.lower()]
   if found:hits.append({'path':p.name,'line':i,'terms':found,'excerpt':l[:1200]})
 R['keyword_screens'][str(row['mathdb_id'])]={'patterns':patterns,'hits':hits,'scope':'Raw projects.yml and candidates files at pinned HEAD; generic keyword hits are not proof matches.'}
R['github_search_hits']=[json.loads(p.read_text()) for p in sorted((D/'sources').glob('github-query-*.json'))]
R['omega_path_screens']={}
for p in (D/'sources').glob('omega-*.json'):
 if p.name not in ['omega-D5.json','omega-Problems.json']:continue
 o=json.loads(p.read_text());R['omega_path_screens'][p.name]={'truncated':o.get('truncated'),'entries':len(o['tree']),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':[x['path'] for x in o['tree'] if any(w in x['path'].lower() for w in ['alternating','hecke','squarefree','square-free','opolynomial','o-polynomial','progression','signedsubset','rainbowmatching','mycielski','flexib','riordan'])]}
R['limitation']='Eight spaced arXiv-ID-plus-lean repository queries returned zero hits; no separate author/name queries due to eight-query ceiling. Pool metadata keyword screen and Omega paths only, not complete proof-body clearance.'
(D/'outputs/registry-screen.json').write_text(json.dumps(R,indent=2))
print('history filtered',len(hist));print('\n'.join(hist[:12]));print('pool project bytes',(D/'sources/pool-projects.yml').stat().st_size)
