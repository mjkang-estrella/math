exec((__import__('pathlib').Path(__file__).parent/'read.py').read_text().split("get('sahbi.raw'")[0])
head=json.loads((L/'sources/omega-HEAD.json').read_bytes())['sha']
for i,p in enumerate(['Blueprint/D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.md','D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.lean']):get(f'proof-body-{i}.txt',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{p}')
(L/'bodies-http.json').write_text(json.dumps(records,indent=2))
