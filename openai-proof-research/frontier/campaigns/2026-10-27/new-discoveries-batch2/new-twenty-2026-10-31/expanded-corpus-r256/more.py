import pathlib,json
L=pathlib.Path(__file__).resolve().parent
r=json.loads((L/'literal-records.json').read_text()); done=['1407.2823','1408.2584','1409.2742','1409.6065']
a=sorted(set(x['record']['source_url'].rsplit('/',1)[-1] for x in r.values())-set(done))
j=[[s+'.pdf','https://arxiv.org/pdf/'+s] for s in a]+[[s+'.abs.html','https://arxiv.org/abs/'+s] for s in a]
j.extend([['spectral-proof.pdf','https://arxiv.org/pdf/1810.01189'],['spectral-proof.abs.html','https://arxiv.org/abs/1810.01189']]);(L/'jobs3.json').write_text(json.dumps(j))
