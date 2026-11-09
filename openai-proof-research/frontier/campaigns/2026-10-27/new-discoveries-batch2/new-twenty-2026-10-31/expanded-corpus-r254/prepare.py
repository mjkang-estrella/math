import pathlib,json
L=pathlib.Path(__file__).resolve().parent
r=json.loads((L/'literal-records.json').read_text()); ids=sorted({v['record']['source_url'].split('/')[-1] for v in r.values()})
jobs=[(a+'-pdf','https://arxiv.org/pdf/'+a) for a in ids]+[(a+'-abs','https://arxiv.org/abs/'+a) for a in ids]
(L/'source-jobs.json').write_text(json.dumps(jobs))
