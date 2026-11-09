import pathlib,itertools,json
W=pathlib.Path(__file__).resolve().parents[1]
exec((W/'scripts/compute.py').read_text().split('rows=[];counts={}')[0])
for trials,pos in enumerate(itertools.combinations(range(1,18),5),1):
 r=mp2(34,pos)
 if r and r['mp']==2:
  (W/'order34.json').write_text(json.dumps(dict(trials=trials,certificate=r),indent=2));print(trials,pos);break
else:print('no witness in all 5-jump sets')
