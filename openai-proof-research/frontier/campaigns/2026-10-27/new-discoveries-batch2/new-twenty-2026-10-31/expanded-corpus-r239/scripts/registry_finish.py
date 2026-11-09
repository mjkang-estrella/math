import pathlib,json,importlib.util
D=pathlib.Path(__file__).resolve().parents[1];sp=importlib.util.spec_from_file_location('lh',D/'scripts/http.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=json.loads((D/'sources/Vilin97-lean-pool-head.json').read_text())['sha'];h.get('lean-pool-projects.yml',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/LeanPool/projects.yml')
terms=['courant','pagenumber','coset factor','braiding','shareshian','rainbow matching','power domination','unicyclic','snark','domes','gain-graphic','coprime graph','schmidt rank','stern poset','quidd','one_third_two_thirds']
s=(D/'sources/lean-pool-projects.yml').read_text();hits=[l for l in s.splitlines() if any(z in l.lower() for z in terms)];(D/'registry-project-hits.json').write_text(json.dumps(hits,indent=2)+'\n');print(hits)
