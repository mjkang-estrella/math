import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];x=json.loads((L/'evidence/complete-registry-path-screen.json').read_text())
for k,v in x.items():
 print(k,v['truncated'],v['count'])
 print('\n'.join(p for p in v['hits'] if any(t in p.lower() for t in ['antipower','naples','wenzel','spider','morse-link','chorded','graver','rainbow','reticulation','signed-sum','power-domination','hamming']) and ('README' in p or k!='openai-preprints-complete'))[:6000])
