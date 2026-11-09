import json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[1];pat=re.compile(r'pop.?stack|clar|polyomino|pointed|eternal|star.?complement|independent.?set|lu.?wenzel|wolff|whiteley|cofactor|loneliness|rainbow.?induced|chromatic.?symmetric.?homology|complete.?sets|loebl|mycielski|unstable|waerden',re.I)
out={}
for k in ['leanpool','openai','omega']:
 t=json.loads((D/'sources'/f'{k}-tree/body').read_text());out[k]={'truncated':t.get('truncated'),'matches':[v['path'] for v in t.get('tree',[]) if pat.search(v['path'])]}
(D/'registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
