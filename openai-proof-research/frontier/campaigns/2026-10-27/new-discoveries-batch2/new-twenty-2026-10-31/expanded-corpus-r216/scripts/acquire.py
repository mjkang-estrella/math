import runpy,pathlib,json,sys
L=pathlib.Path(__file__).resolve().parents[1]; f=runpy.run_path(str(L/'scripts/fetch.py'))['fetch']
mode=sys.argv[1]
if mode=='registry':
 for n,repo in [(1,'Vilin97/lean-pool'),(2,'openai/math'),(3,'the-omega-institute/trureturing')]:
  sha=json.loads((L/f'sources/http-{n:04d}.bin').read_bytes())['sha'];print(repo,sha,flush=True)
  f(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1')
  if n==1:f(f'https://raw.githubusercontent.com/{repo}/{sha}/projects.yml')
else:
 rows=json.loads((L/'reservation.json').read_text())['rows']
 for r in rows[int(sys.argv[2]):int(sys.argv[3])]:
  u=r['source_url'];f(u)
  if 'arxiv.org/abs/' in u:f(u.replace('/abs/','/pdf/'))
