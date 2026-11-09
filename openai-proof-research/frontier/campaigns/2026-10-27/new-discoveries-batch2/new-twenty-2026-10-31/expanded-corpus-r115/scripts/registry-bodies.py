from fetch import get,D
import json
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
for name in ['shin-four-point-sumset-compression.md','gurvich-krnc-vyalyi-conjecture-1-total-amoeba-confinement.md']:
 print(get((name,f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/Problems/{name}')))
