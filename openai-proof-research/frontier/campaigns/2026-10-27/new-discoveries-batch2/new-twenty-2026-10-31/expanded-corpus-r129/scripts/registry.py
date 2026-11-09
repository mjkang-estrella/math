import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'))
from fetch import get
for name,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 h=json.loads((D/f'sources/{name}-head.json').read_text())['sha']
 print(get((f'{name}-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{h}?recursive=1')),flush=True)
