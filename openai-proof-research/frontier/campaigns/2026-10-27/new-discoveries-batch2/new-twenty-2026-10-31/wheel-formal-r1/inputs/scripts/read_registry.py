from fetch import get,D
import json
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
for key,p in [('cycle-star-proof.lean','D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.lean'),('cycle-star-problem.md','Problems/cycle-star-irregularity.md')]:print(get((key,'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+p)))
