import pathlib,json
r=pathlib.Path(__file__).resolve().parents[1]
for p in (r/'http').glob('*/receipt.json'):
 d=json.loads(p.read_text()); u=d['url']
 if 'commits/HEAD' in u:
  j=json.loads((p.parent/'body').read_text());print(u,j['sha'],j['commit']['committer']['date'])
j=json.loads((r/'logs/check.json').read_text());print(json.dumps(j['search'],indent=2));print('robust',j['robust']);print('family',j['family_checks'])
