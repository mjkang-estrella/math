import pathlib,json,re
L=pathlib.Path(__file__).resolve().parents[1];terms=['quadratic','fibonacci','antipower','young','signedsum','signed-sum','spider','morse','wenzel','naples','reticulation','ryser','rainbow','powerdomination','power-domination','krattenthaler','parabolic','finwing','robustness','graver','chorded','incidence','hamming']
out={}
for name in ['omega-D5-scope','omega-Problems-complete','openai-preprints-complete']:
 p=L/f'sources/{name}/body';x=json.loads(p.read_text());out[name]={'truncated':x.get('truncated'),'count':len(x.get('tree',[])),'hits':[r['path'] for r in x.get('tree',[]) if any(t in r['path'].lower() for t in terms)]}
(L/'evidence/complete-registry-path-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:17000])
