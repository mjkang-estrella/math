import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'reservation.json').read_text());papers=sorted(set(r['source_url'].rsplit('/',1)[1] for r in x['rows']))
(D/'abs-plan.json').write_text(json.dumps([(a+'-abs.html','https://arxiv.org/abs/'+a) for a in papers]))
repos=['Vilin97/lean-pool','openai/math','the-omega-institute/trureturing']
(D/'registry-plan.json').write_text(json.dumps([(r.split('/')[0]+'-head.json','https://api.github.com/repos/'+r+'/commits/HEAD') for r in repos]))
