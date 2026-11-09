import pathlib,json
L=pathlib.Path(__file__).resolve().parent;B=L.parent
for x in json.loads((B/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text())['families']:print(x['number'],x['title'],x.get('scope',''))
h=json.loads((B/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text());print(json.dumps(h,ensure_ascii=False))
