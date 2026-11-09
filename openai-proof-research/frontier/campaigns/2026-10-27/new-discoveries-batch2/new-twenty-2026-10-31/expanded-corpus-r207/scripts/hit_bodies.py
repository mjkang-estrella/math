from pathlib import Path
import json,importlib.util
L=Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',L/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
for label,repo in [('frustration-registry-hit','velvetmonkey/oph-gap-lean'),('triality-registry-hit','dupuisf/lean4-experimentation')]:
 sha=json.loads(next((L/'sources').glob(label+'-*/body')).read_text())['sha'];b,r,p=f.fetch(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1',label+'-tree')
 for x in json.loads(b).get('tree',[]):
  if x['path'].lower() in ['readme.md','readme']:f.fetch(f'https://raw.githubusercontent.com/{repo}/{sha}/{x["path"]}',label+'-readme')
