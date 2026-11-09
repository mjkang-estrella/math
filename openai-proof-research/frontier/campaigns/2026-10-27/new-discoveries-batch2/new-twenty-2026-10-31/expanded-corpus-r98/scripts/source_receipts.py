from fetch import get,D
import json
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
for p in ['Problems/rectangle-rowmotion-max-minus-min-homomesy.md','Problems/bhoria-eyyunni-santra-2026-overpartition-threshold-identity.md','D5/S3/Factorization/MarkovEquationMutation.lean']:
 print(get(('registry-'+p.rsplit('/',1)[-1],f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/{p}')))
print(get(('matrix-published.pdf','https://alco.centre-mersenne.org/item/10.5802/alco.406.pdf')))
