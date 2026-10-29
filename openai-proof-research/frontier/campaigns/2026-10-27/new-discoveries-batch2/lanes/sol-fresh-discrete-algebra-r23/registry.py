from fetch import *
p=b.parent
out={}
for name,repo,base in [('openai','openai/math',p/'sol-mean-cascade-current-prior-audit-r1/sources/openai-preprints-tree.json'),('count','suvrit/count-ex-machina',p/'sol-mean-cascade-current-prior-audit-r1/sources/count-full-tree.json'),('aim','MColbrook/AIM',p/'root-log-arctangent-acceptance-r1/aim-screen/tree.json')]:
 h=json.loads((b/'sources'/f'{name}-head.json').read_text());j=json.loads(base.read_text())
 out[name]={'head':h['sha'],'commit_utc':h['commit']['committer']['date'],'base_file':str(base),'sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'entries':len(j['tree']),'truncated':j.get('truncated'),'coverage':'unchanged verified live head; complete saved tree'}
 assert j.get('truncated')==False
root=fetch('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+json.loads((b/'sources/omega-head.json').read_text())['commit']['tree']['sha'])
if root:
 out['omega']={'head':json.loads((b/'sources/omega-head.json').read_text())['sha'],'trees':[]}
 for e in root['tree']:
  if e['type']!='tree':continue
  n='omega-'+e['path'].replace('/','_')+'-tree.json'
  bases=list((p/'sol-fresh-probability-finite-r21/sources').glob(n))
  j=json.loads(bases[0].read_text()) if bases else {}
  if j.get('sha')==e['sha'] and j.get('truncated')==False: loc=bases[0]
  else:
   j=fetch(n,'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+e['sha']+'?recursive=1');loc=b/'sources'/n
  if not j:out['omega']['gap']=True;break
  out['omega']['trees'].append({'prefix':e['path'],'file':str(loc),'entries':len(j.get('tree',[])),'truncated':j.get('truncated'),'sha':j.get('sha'),'sha256':hashlib.sha256(loc.read_bytes()).hexdigest()})
(b/'registry.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
