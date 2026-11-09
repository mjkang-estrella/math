import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'outputs/registry-screen.json').read_text())
for name in ['pool','omega','openai']:
 print(name,x[name]['sha'],x[name]['truncated'],x[name]['path_count'])
 for i,v in x[name]['screen'].items():
  hits=[z for z in v['hits'] if i in z or i not in ['375631'] and any(w in z.lower() for w in ['jacobi','tanigawa','heged','liwski','statistic373','zhangmisener','acyclichero','sperner'])]
  if hits:print(i,hits[:8])
print('GitHub',[(q.get('status'),q.get('total_count')) for q in x['github_repository_search']])
