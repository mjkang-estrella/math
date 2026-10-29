exec((__import__('pathlib').Path(__file__).parent/'audit.py').read_text().split("if sys.argv[1] in")[0])
receipts=[]
def fetch(n,u):
 r=get(n,u);receipts.append(r);(b/'http-trees.json').write_text(json.dumps(receipts,indent=2));return json.loads((b/'sources'/n).read_text()) if 'error' not in r else {}
summary={}
for n,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math'),('count','suvrit/count-ex-machina')]:
 h=json.loads((b/'sources'/(n+'-head.json')).read_text());summary[n]={'head':h['sha'],'commit_utc':h['commit']['committer']['date']}
 root=fetch(n+'-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+h['commit']['tree']['sha'])
 summary[n]['root']=root.get('sha');summary[n]['trees']=[]
 targets=['D5','Problems'] if n=='omega' else ['preprints'] if n=='openai' else []
 if n=='count':
  j=fetch(n+'-full-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+root['sha']+'?recursive=1');summary[n]['trees'].append({'file':n+'-full-tree.json','entries':len(j.get('tree',[])),'truncated':j.get('truncated')})
 else:
  for e in root.get('tree',[]):
   if e['path'] in targets:
    f=n+'-'+e['path']+'-tree.json';j=fetch(f,'https://api.github.com/repos/'+repo+'/git/trees/'+e['sha']+'?recursive=1');summary[n]['trees'].append({'file':f,'sha':e['sha'],'entries':len(j.get('tree',[])),'truncated':j.get('truncated')})
(b/'registry-completeness.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary,indent=2))
