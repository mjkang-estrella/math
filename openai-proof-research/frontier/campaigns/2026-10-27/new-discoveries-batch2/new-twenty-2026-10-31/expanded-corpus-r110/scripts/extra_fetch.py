from fetch import get,D
import json
for a in ['2606.23250v1','2308.07240','2601.12036']:
 print(get((a+'.html','https://arxiv.org/html/'+a)),flush=True)
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
for name in ['PrefixReversalTripleEvenNonGeneration','PrefixReversalTripleOddNonGeneration']:
 print(get((name+'.lean',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/D5/S0/CayleyGrowth/{name}.lean')),flush=True)
