from fetch import D,get
import json
head=json.loads((D/'sources/openai-head.json').read_text())['sha'];prefix='A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/'
for f in ['00-introduction.tex','01-reduction.tex','02-pruning.tex','03-incompatibility.tex','04-weighted-consequences.tex']:
 print(get(('seymour-'+f,'https://raw.githubusercontent.com/openai/math/'+head+'/preprints/'+prefix+f)),flush=True)
