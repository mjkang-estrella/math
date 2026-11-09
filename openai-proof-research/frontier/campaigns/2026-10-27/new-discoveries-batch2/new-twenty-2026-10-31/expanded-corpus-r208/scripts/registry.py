import pathlib,json,importlib.util
D=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('lanehttp',D/'scripts/http.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
for key,repo in [('leanpool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing')]:
 sha=json.loads((D/'sources'/f'{key}-head.json').read_text())['sha'];m.get(key+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1')
 if key=='leanpool':m.get('leanpool-projects.yml',f'https://raw.githubusercontent.com/{repo}/{sha}/projects.yml')
