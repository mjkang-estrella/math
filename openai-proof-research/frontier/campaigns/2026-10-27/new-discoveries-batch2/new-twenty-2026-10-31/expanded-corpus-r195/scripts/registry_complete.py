import pathlib,json,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
def get(n,u):subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),n,u],check=True)
for name,repo,wanted in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints'])]:
 h=json.loads((D/f'sources/{name}-head.body').read_text())['sha'];get(name+'-root',f'https://api.github.com/repos/{repo}/git/trees/{h}')
 for z in json.loads((D/f'sources/{name}-root.body').read_text())['tree']:
  if z['path'] in wanted:get(name+'-'+z['path'],f'https://api.github.com/repos/{repo}/git/trees/{z["sha"]}?recursive=1')
