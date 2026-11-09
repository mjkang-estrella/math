import json,pathlib
P=pathlib.Path(__file__).resolve().parents[1]
a=json.loads((P/'downloads/request-000/body').read_text());print('OpenAlex',a['id'],a['cited_by_count'],a.get('cited_by_api_url'));print('authors',[(x['author']['id'],x['author']['display_name']) for x in a['authorships']])
for num in ['004','005']:
 a=json.loads((P/f'downloads/request-{num}/body').read_text());print('registry',a['sha'],a['commit']['committer']['date'],a['commit']['tree']['sha'])
for num in ['006','007']:
 a=json.loads((P/f'downloads/request-{num}/body').read_text());print('OpenAlex result',num,'count',a['meta']['count'])
 for x in a['results']:print(x['id'],x.get('doi'),x['publication_date'],x['title'])
a=json.loads((P/'downloads/request-011/body').read_text())
for e in a['tree']:
 if e['path'] in ['D5','Problems']:print('tree',e['path'],e['sha'],e['url'])
a=json.loads((P/'downloads/request-006/body').read_text())
for x in a['results']:
 print('CITING LOCATIONS',x['title'],[(y.get('landing_page_url'),y.get('pdf_url')) for y in x['locations']])
for num in ['013','014']:
 a=json.loads((P/f'downloads/request-{num}/body').read_text());paths=[e['path'] for e in a['tree']];print('REGISTRY TREE',num,len(paths),a.get('truncated'))
 print('PATH MATCHES',[s for s in paths if any(w in s.lower() for w in ['jeffries','yeats','352253','delta','wye'])])
