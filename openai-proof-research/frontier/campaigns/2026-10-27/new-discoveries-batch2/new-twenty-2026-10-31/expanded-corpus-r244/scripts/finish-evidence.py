import json,pathlib,ast
D=pathlib.Path(__file__).resolve().parents[1]
rows=[]
for line in (D/'logs/pointed-8-10.log').read_text().splitlines():
 if line.startswith('{'):rows.append(ast.literal_eval(line))
(D/'pointed-completed-8-9.json').write_text(json.dumps({'completed_rows':rows,'n10':'incomplete; CPU 120s cap; no full coverage claimed'},indent=2))
h=json.loads((D/'sources/openai-head/body').read_text())['sha'];todo=[('https://raw.githubusercontent.com/openai/math/'+h+'/lean/ComparatorChallenges/IndependentSets.'+s,'openai-independent-'+s) for s in ['lean','json']]
(D/'fetch-comparator.json').write_text(json.dumps(todo))
r=json.loads((D/'sources/openai-preprints/body').read_text());paths=[p['path'] for p in r['tree']];(D/'openai-preprints-screen.json').write_text(json.dumps({'truncated':r.get('truncated'),'head':h,'screen':'filename/topic screening only; no worldwide or full-body clearance','matches':[p for p in paths if any(w in p.lower() for w in ['pointed','clar-','eternal','pop-stack','independent-set','wolff','whiteley','cofactor','rainbow-induced','star-complement'])]},indent=2))
