exec(open('refresh.py').read().split('repos=')[0].replace("records=[]","records=json.loads(Path('http.json').read_text())"))
head=json.loads((D/'omega-head.json').read_text())['sha'];base='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'
# Fetch as bytes, preserving headers/status and SHA; get() parses only JSON, so use dedicated raw function.
def raw(url,name):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=25) as r:data=r.read();status=r.status
  (D/name).write_bytes(data);records.append(dict(url=url,utc=t,status=status,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
 except Exception as e:records.append(dict(url=url,utc=t,error=str(e)))
 Path('http.json').write_text(json.dumps(records,indent=2))
raw(base+'D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.lean','LPolyomino.lean')
raw(base+'D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.lean','Domino.lean')
raw(base+'Problems/condon-dugan-goldman-williams-2026-l-polyomino-skipped-sequence.md','LProblem.md')
raw(base+'Problems/mathar-2024-nonbonding-domino-pairs.md','DominoProblem.md')
# Full named-tree difference from r3, not a capped compare API.
old=json.loads(Path('extracted/evidence/sol-polyomino57-source-prior-refresh-r3/live/omega-D5.json').read_text()) if Path('extracted/evidence/sol-polyomino57-source-prior-refresh-r3/live/omega-D5.json').exists() else None
if old:
 a={x['path']:x['sha'] for x in old['tree'] if x['type']=='blob'};new=json.loads((D/'omega-D5.json').read_text());delta=[x['path'] for x in new['tree'] if x['type']=='blob' and a.get(x['path'])!=x['sha']]
 Path('r3-current-delta.json').write_text(json.dumps(delta,indent=2))
 for i,p in enumerate(delta):raw(base+'D5/'+p,'r3delta-'+str(i)+'.lean')
