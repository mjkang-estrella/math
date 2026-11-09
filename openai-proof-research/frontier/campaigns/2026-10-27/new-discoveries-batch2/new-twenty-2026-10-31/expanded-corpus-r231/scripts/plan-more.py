import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];t=[]
for p in (D/'sources').glob('*-head.json'):
 o=json.loads(p.read_text());repo=o['url'].split('/repos/')[1].split('/commits/')[0];sha=o['sha'];t.append((p.name.replace('head','tree'),'https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1'))
for p in (D/'sources').glob('*-abs.html'):
 a=p.name.split('-abs')[0];s=p.read_text();m=re.search(r'arXiv:'+re.escape(a)+r'v(\d+)',s)
 if m:
  for v in range(1,int(m[1])+1):t.append((a+'v'+str(v)+'.pdf','https://arxiv.org/pdf/'+a+'v'+str(v)))
for a in ['2609.02763','2609.07481','2609.04069','2605.20184']:
 t.extend([(a+'-abs.html','https://arxiv.org/abs/'+a),(a+'.pdf','https://arxiv.org/pdf/'+a)])
(D/'fetch-more.json').write_text(json.dumps(t,indent=2)+'\n')
