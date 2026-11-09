from fetch import *
r=json.loads((BASE/'sources/omega-root.json').read_text())
for n in ['D5','Problems']:
 e=next(x for x in r['tree'] if x['path']==n)
 t=fetch(e['url']+'?recursive=1','omega-'+n+'-tree.json')
 print(n,'truncated',t.get('truncated'),'entries',len(t['tree']))
 hits=[x for x in t['tree'] if any(w in x['path'].lower().replace('_','').replace('-','') for w in ['marginal','loglinear','collaps','subdivision','tropical','dressian','378395','fienberg','rinaldo'])]
 (BASE/'outputs'/('omega-'+n+'-hits.json')).write_text(json.dumps(hits,indent=2))
 for i,e in enumerate(hits):
  if e['type']=='blob':fetch('https://raw.githubusercontent.com/the-omega-institute/trureturing/'+r['sha']+'/'+n+'/'+e['path'],'omega-hits/'+n+'-'+str(i)+'.txt')
