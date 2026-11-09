import sys,json,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch_http import get
D=pathlib.Path(__file__).resolve().parents[1];sha=json.loads((D/'http/openai-head.json').read_text())['sha']
for p in ['preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/01-introduction.tex','preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/07-consequences.tex','preprints/the-additive-indecomposability-of-the-primes-September-24-2026/build/main.tex']:
 get('prior-'+p.split('/')[1]+'-'+p.split('/')[-1],f'https://raw.githubusercontent.com/openai/math/{sha}/{p}')
