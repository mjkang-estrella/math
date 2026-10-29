import pathlib,json,urllib.request,datetime,hashlib
D=pathlib.Path(__file__).resolve().parent
j=json.loads((D/'research/omega-head.json').read_text());print('Omega',j['sha'],j['commit']['committer']['date']);print('OpenAI',json.loads((D/'research/openai-head.json').read_text())['sha'])
url='https://api.github.com/repos/the-omega-institute/trureturing/compare/e9c949019b00eb22ab88e81d6ac6b1047925d95d...'+j['sha']
rows=[]
try:
 with urllib.request.urlopen(url,timeout=25) as r:b=r.read()
 (D/'research/omega-new-compare.json').write_bytes(b);c=json.loads(b)
 rows.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':hashlib.sha256(b).hexdigest(),'status':200,'total_commits':c['total_commits'],'files':len(c.get('files',[]))})
 print([(f['filename'],f.get('patch','')[:300]) for f in c.get('files',[])])
except Exception as e:rows.append({'url':url,'error':str(e)})
(D/'research/current-access.json').write_text(json.dumps(rows,indent=2))
# Save bounded exact path selection and baseline metadata, without treating paths as semantic clearance.
B=D.parent/'root-edge-irregulator-final-freeze-r1'
(D/'research/baseline-registry.json').write_bytes((B/'CURRENT-REGISTRIES.json').read_bytes())
for n in ['omega-tree.txt','openai-tree.txt','openai-CONTENTS.md']:
 lines=(B/n).read_text().splitlines(); matches=[l for l in lines if any(x in l.lower() for x in ['bajnok','beatty','dougherty','faber','lee-sphere','leesphere','cayleygraph','cayley-graph'])]
 (D/'research'/('matches-'+n)).write_text('\n'.join(matches))
 print(n,'matched lines',len(matches))
