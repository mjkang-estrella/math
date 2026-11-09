import json,re
from fetch import D,get
head=json.loads((D/'sources/omega-head.json').read_text())['sha']
for p in ['Problems/garcia-marco-2025-uniform-toeplitz-factorization.md','D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.lean','Problems/lichtenfelz-modin-preston-2026-zeitlin-ricci-limit.md','D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.lean']:
 print(get((p.split('/')[-1],'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+p)))
# Exact-ID and subject path screen, not proof-body clearance.
patterns=[str(i) for i in json.loads((D/'reservation.json').read_text())['ids']]+['luroth','lüroth','zero.sum','toeplitz','thrackle','path.perfect','equiangular','zeitlin','connected.domina','odd.cover','backbone','distinguish','rainbow','outerplane','radical','telescope','xeric','difference.multiset','igusa']
records={}
for name in ['D5','Problems']:
 d=json.loads((D/f'sources/omega-{name}-tree.json').read_text());records[name]={'truncated':d['truncated'],'entries':len(d['tree']),'hits':[x['path'] for x in d['tree'] if any(re.search(p,x['path'],re.I) for p in patterns)]}
(D/'outputs/registry-path-screen.json').write_text(json.dumps(records,indent=2)+'\n')
