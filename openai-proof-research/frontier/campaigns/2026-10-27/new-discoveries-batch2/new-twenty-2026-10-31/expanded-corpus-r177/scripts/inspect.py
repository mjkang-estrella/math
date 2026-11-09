import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('github-search-?.json')):
 o=json.loads(p.read_text());print(p.name,[(x['full_name'],x['description']) for x in o.get('items',[])])
