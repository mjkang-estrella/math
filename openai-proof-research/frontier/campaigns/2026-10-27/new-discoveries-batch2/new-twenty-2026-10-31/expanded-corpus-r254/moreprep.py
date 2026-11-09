import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent;j=[]
for k,r in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 h=json.loads((L/(k+'-head.body')).read_text())['sha'];j.append((k+'-root','https://api.github.com/repos/'+r+'/git/trees/'+h))
 if k=='openai':j.append(('openai-readme','https://raw.githubusercontent.com/'+r+'/'+h+'/README.md'))
 d=json.loads((L/(k+'-tree.body')).read_text())
 if k=='pool':
  for x in d['tree']:
   if x['type']=='blob' and re.search(r'(candidate|index)',x['path'],re.I) and not x['path'].endswith('.lean'):
    print('poolindex',x['path']);j.append(('pool-index-'+str(len(j)),'https://raw.githubusercontent.com/'+r+'/'+h+'/'+x['path']))
 if k=='omega':
  d=json.loads((L/'omega-subtree-D5.body').read_text());print('D5 truncated',d.get('truncated'))
  for x in d['tree']:
   if re.search('ArrowWilf|Gilbreath|Semiacyclic|ZeroDivisor|TwoStack|TreeLike|StirlingPerm',x['path'],re.I) and x['type']=='blob' and (x['path'].endswith('.result') or x['path'].endswith('.lean')):
    print('matched',x['path']);j.append(('omega-match-'+str(len(j)),'https://raw.githubusercontent.com/'+r+'/'+h+'/D5/'+x['path']))
(L/'more-jobs.json').write_text(json.dumps(j))
