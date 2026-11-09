import json,importlib.util,urllib.parse,time
from pathlib import Path
L=Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',L/'scripts/fetch.py'); f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
queries=['"2607.02239" lean','"triality" "lean"','"frustration" "lean"','"132" "adjacency" "lean"','"copious" "lean"','"edge inducibility" "lean"','"weak excedance" "lean"','"Ising" "unicellular" "lean"'];out=[]
for q in queries:
 b,r,p=f.fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search');out.append({'query':q,'receipt':p,'status':r.get('status'),'body':json.loads(b) if b else None})
 if r.get('status') in (403,429): break
 time.sleep(8)
(L/'outputs/github-search.json').write_text(json.dumps(out,indent=2))
