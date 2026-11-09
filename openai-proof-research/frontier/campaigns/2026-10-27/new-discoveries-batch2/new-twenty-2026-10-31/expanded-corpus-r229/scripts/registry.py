import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1]
pat=re.compile(r'357590|357600|357610|357636|357678|357745|357791|357805|357806|357850|357880|358018|358043|358112|358220|358308|358355|358391|358524|358525|Sokal|Roudneff|Aharoni|Painlev|Upset|Bipart|NonCross|Immersion|Permuto|DistanceMagic|Phylogen',re.I)
out={}
for p in (D/'sources').glob('*tree.json'):
 o=json.loads(p.read_text());out[p.name]={'sha':o.get('sha'),'truncated':o.get('truncated'),'path_count':len(o.get('tree',[])),'matches':[x['path'] for x in o.get('tree',[]) if pat.search(x['path'])]}
(D/'evidence/registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:10000])
