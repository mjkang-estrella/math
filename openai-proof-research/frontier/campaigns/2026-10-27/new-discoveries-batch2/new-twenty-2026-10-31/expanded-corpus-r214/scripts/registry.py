import pathlib,json,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
for k in ['pool','omega','openai']:
 o=json.loads((D/'sources'/f'{k}-head.json').read_text());print(k,o.get('sha'))
sha=json.loads((D/'sources/pool-head.json').read_text())['sha']
get('pool-tree.json',f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{sha}?recursive=1')
get('pool-projects.yml',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/projects.yml')
