from fetch import *
base=b.parent/'sol-mean-cascade-current-prior-audit-r1'/'sources'
summary={}
for n,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math'),('count','suvrit/count-ex-machina')]:
 h=json.loads((b/'sources'/(n+'-head.json')).read_text());old=json.loads((base/(n+'-head.json')).read_text());summary[n]={'current':h['sha'],'base':old['sha'],'commit_utc':h['commit']['committer']['date'],'base_evidence':str(base),'unchanged':h['sha']==old['sha']}
 if n=='omega' and h['sha']!=old['sha']:
  get('omega-delta.json','https://api.github.com/repos/'+repo+'/compare/'+old['sha']+'...'+h['sha'])
  j=json.loads((b/'sources'/'omega-delta.json').read_text());summary[n].update(total_commits=j.get('total_commits'),returned_commits=len(j.get('commits',[])),changed_files=len(j.get('files',[])))
  # compare file lists may truncate: use fresh subtree hashes and untruncated trees
  get('omega-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+h['commit']['tree']['sha'])
  root=json.loads((b/'sources'/'omega-root.json').read_text());summary[n]['trees']=[]
  for e in root['tree']:
   if e['path'] in ['D5','Problems']:
    f='omega-'+e['path']+'-tree.json';get(f,'https://api.github.com/repos/'+repo+'/git/trees/'+e['sha']+'?recursive=1');t=json.loads((b/'sources'/f).read_text());summary[n]['trees'].append({'file':f,'sha':t['sha'],'entries':len(t['tree']),'truncated':t['truncated']})
(b/'registry.json').write_text(json.dumps(summary,indent=2));print(summary)
