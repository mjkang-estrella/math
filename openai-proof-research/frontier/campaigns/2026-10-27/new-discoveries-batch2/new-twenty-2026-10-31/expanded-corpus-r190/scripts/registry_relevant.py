import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'outputs/registry-screen.json').read_text())
for i in ['334235','334318','334519','334926','373247','330175','330268','330331']:
 print('ID',i)
 x=r['screens'][i]
 for z in x['path_screens']:
  if len(z['hits'])<25:print(z['name'],z['hits'])
 for z in x['leanpool_body_hits'][:20]:print(z['text'])
