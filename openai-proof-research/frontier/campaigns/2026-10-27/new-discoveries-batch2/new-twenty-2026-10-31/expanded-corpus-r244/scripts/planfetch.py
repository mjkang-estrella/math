import json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());todo=[]
for i,o in x.items():
 t=(D/'sources'/f'{i}-abs/body').read_text(); vs=sorted(set(re.findall(r'/abs/(\d+\.\d+v\d+)',t)))
 if not vs: vs=[o['source_url'].rsplit('/',1)[-1]+'v1']
 for v in vs:todo.append(('https://arxiv.org/pdf/'+v,i+'-'+v+'-pdf'))
 print(i,vs)
for k in ['leanpool','openai','omega']:
 h=json.loads((D/'sources'/f'{k}-head/body').read_text());print(k,h.get('sha'));repo={'leanpool':'Vilin97/lean-pool','openai':'openai/math','omega':'the-omega-institute/trureturing'}[k];todo.append(('https://api.github.com/repos/'+repo+'/git/trees/'+h['sha']+'?recursive=1',k+'-tree'))
(D/'fetch-pdf.json').write_text(json.dumps(todo))
