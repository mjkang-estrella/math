import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1]
for n in ['openai-head','omega-head']:
 d=json.loads((L/'downloads'/n/'body').read_text()); print(n,d['sha'],d['commit']['committer']['date'])
d=json.loads((L/'downloads/openalex/body').read_text())
print('OpenAlex matches',d.get('meta',{}).get('count'))
for r in d.get('results',[]): print(r['id'],r['title'],r.get('cited_by_count'),r.get('doi'))
