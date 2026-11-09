from pathlib import Path
import re,json
L=Path(__file__).resolve().parent;D=L/'http'
pat=re.compile(r'hamada|queen|stahl|kneser|gessel|zhuang|peakrefin|peak.refin|starforest|star.forest|wanless|latinhyper|latin.hyper|dewar|antidirect|agrawal|triplearray|triple.array|trianglefree.*cycl|triangle.free.*cycl|adjacencydimension|adjacency.dimension|extendab|bowtie|bow.tie|cyclewheel|cycle.wheel|graphimmersion|graph.immersion|mubayi|skewsymm|skew.symm|signedperm|signed.perm|laplacianp|laplacian.p|recalcitr|macedon',re.I)
out={};j=[]
for name in ['openai-preprints-complete','omega-D5-tree','omega-Problems-tree','omega-Reg-tree','pool-tree']:
 p=D/(name+'.json')
 if not p.exists():continue
 t=json.loads(p.read_text());hits=[x for x in t['tree'] if pat.search(x['path'])];out[name]={'truncated':t.get('truncated'),'count':len(t['tree']),'hits':hits};print(name,t.get('truncated'),len(hits));print('\n'.join(x['path'] for x in hits)[:5500])
 for x in hits:
  if x['type']=='blob' and x['path'].endswith(('.md','.lean','.cs','.tex')):
   if name.startswith('omega'):
    pre={'omega-D5-tree':'D5/','omega-Problems-tree':'Problems/','omega-Reg-tree':'Reg/'}[name];j.append(['matched-'+pre.replace('/','--')+x['path'].replace('/','--'),'https://raw.githubusercontent.com/the-omega-institute/trureturing/1c3e22220746be4f0b18e51689b333dc025c36ab/'+pre+x['path']])
for p in list(D.glob('pool-candidate-*'))+[D/'pool-projects.yml']:
 if p.name.endswith('.json.receipt.json') or p.name.endswith('.receipt.json'):continue
 try:ls=[{'line':n,'text':s[:2000]} for n,s in enumerate(p.read_text().splitlines(),1) if pat.search(s)]
 except Exception:continue
 out[p.name]={'hits':ls};print(p.name,len(ls));print(str(ls)[:2000])
(L/'registry-final-screen.json').write_text(json.dumps(out,indent=2));(L/'matched-plan.json').write_text(json.dumps(j));print('matched jobs',len(j))
