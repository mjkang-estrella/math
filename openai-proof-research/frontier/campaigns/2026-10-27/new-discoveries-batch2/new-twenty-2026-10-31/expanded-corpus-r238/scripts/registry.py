import pathlib,json,sys,importlib.util,re
D=pathlib.Path(__file__).resolve().parents[1];spec=importlib.util.spec_from_file_location('lanehttp',D/'scripts/http.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
p=D/'sources/Vilin97-lean-pool-head.json';sha=json.loads(p.read_text())['sha'];h.get('lean-pool-projects.yml',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/projects.yml')
t=json.loads((D/'sources/Vilin97-lean-pool-tree.json').read_text())
for x in t.get('tree',[]):
 if x['path'].startswith('candidates/') and x['type']=='blob':h.get('lean-pool-'+x['path'].replace('/','__'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/'+x['path'])
terms=['spectr','antimagic','polygon','feedback','Bosek','neighborhood','CMPP','heptagon','uncertainty','Waring','Cantor','elongated','eigenpolynomial','inversion','guessing','dominating','Grothendieck','Gao','expansion','Toeplitz','handlebody']
out={}
for p in (D/'sources').glob('*tree.json'):
 t=json.loads(p.read_text());hits=[x['path'] for x in t.get('tree',[]) if any(k.lower() in x['path'].lower() for k in terms)];out[p.name]={'truncated':t.get('truncated'),'hits':hits};print(p.name,len(hits));print('\n'.join(hits)[:10000])
for p in (D/'sources').glob('lean-pool-*'):
 if p.suffix=='.json':continue
 lines=[l for l in p.read_text(errors='replace').splitlines() if any(k.lower() in l.lower() for k in terms)];out[p.name]=lines;print(p.name,'\n'.join(lines)[:4000])
(D/'registry-screen.json').write_text(json.dumps(out,indent=2))
h.get('github-reposearch.json','https://api.github.com/search/repositories?q='+__import__('urllib.parse',fromlist=['quote']).quote('lean ("high-ordered" OR "Gao" OR "feedback game" OR "polygon intersection")'))
