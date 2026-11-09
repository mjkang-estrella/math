import pathlib,json
L=pathlib.Path(__file__).resolve().parent;r=json.loads((L/'records.json').read_text())
(L/'abs-jobs.json').write_text(json.dumps([[i+'.abs.html',a['record']['source_url']] for i,a in r.items()]))
(L/'pdf-jobs.json').write_text(json.dumps([[i+'.pdf',a['record']['source_url'].replace('/abs/','/pdf/')] for i,a in r.items()]))
