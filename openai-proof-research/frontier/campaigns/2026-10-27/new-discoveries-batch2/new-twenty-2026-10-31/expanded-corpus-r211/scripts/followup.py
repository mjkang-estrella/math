import pathlib,sys
P=pathlib.Path(__file__).resolve().parent/'fetch.py';ns={'__name__':'fetch','__file__':str(P)};exec(compile(P.read_text(),str(P),'exec'),ns);get=ns['get'];D=ns['D'];json=ns['json']
sha=json.loads((D/'sources/leanpool-head.json').read_text())['sha'];get('leanpool-projects-pinned.yml',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/LeanPool/projects.yml')
for x in json.loads((D/'sources/leanpool-tree.json').read_text())['tree']:
 if x['type']=='blob' and x['path'].startswith('candidates/'):get('leanpool-'+x['path'].replace('/','_'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/'+x['path'])
for a in ['2609.23779','1706.07208','1307.0158']:
 get(a+'-abs.html','https://arxiv.org/abs/'+a);get(a+'.pdf','https://arxiv.org/pdf/'+a)
for k,q in [('restraint','"restraint" lean'),('competition','"competition graphs" lean'),('nim','"building nim" lean'),('cores','"core partitions" lean'),('typeb','"Shigechi" lean')]:
 import urllib.parse,time
 get('github-search-'+k+'.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q));time.sleep(8)
