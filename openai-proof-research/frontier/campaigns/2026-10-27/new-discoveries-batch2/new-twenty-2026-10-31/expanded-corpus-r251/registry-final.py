from pathlib import Path
import json,re
L=Path(__file__).resolve().parent
T=json.loads((L/'http/leanpool-tree.json').read_text());print('project paths',[x['path'] for x in T['tree'] if x['path'].endswith('projects.yml')])
q=json.loads((L/'http/omega-head.json').read_text());print('omega',q['sha']);print('openai',json.loads((L/'http/openai-head.json').read_text())['sha'])
jobs=[['omega-tree.json',f"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{q['sha']}?recursive=1"],['github-search-flow.json','https://api.github.com/search/repositories?q=%221610.08370%22+lean']]
for x in T['tree']:
 if x['path'].endswith('projects.yml'):jobs.append(['pool-projects-at-path.yml',f"https://raw.githubusercontent.com/Vilin97/lean-pool/{T['sha']}/{x['path']}"])
(L/'registry-final-jobs.json').write_text(json.dumps(jobs))
