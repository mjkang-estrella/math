import pathlib,sys,subprocess,json
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'))
from fetch import get
for key,url in [('maxdescent.pdf','https://www.ms.uky.edu/~jrge/Papers/Maximizing.pdf'),('symmetric-bo.html','https://link.springer.com/article/10.1007/s40687-021-00253-8'),('robin2026.pdf','https://arxiv.org/pdf/2610.34320')]:
 print(get((key,url)),flush=True)
 if key.endswith('.pdf') and (D/'sources'/key).exists():subprocess.run(['pdftotext','-layout',str(D/'sources'/key),str((D/'sources'/key).with_suffix('.txt'))])
# OpenAI exact preprint subtree, current unchanged HEAD
h=json.loads((D/'sources/openai-head.json').read_text())['sha'];repo='openai/math'
print(get(('openai-root.json',f'https://api.github.com/repos/{repo}/git/trees/{h}')),flush=True)
o=json.loads((D/'sources/openai-root.json').read_text())
for x in o['tree']:
 if x['path']=='preprints':print(get(('openai-preprints.json',f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1')),flush=True)
