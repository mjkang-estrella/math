import pathlib,json,sys,urllib.parse,time
D=pathlib.Path(__file__).resolve().parents[1]
exec(compile((D/'scripts/fetch.py').read_text().split("if __name__")[0],str(D/'scripts/fetch.py'),'exec'))
sha=json.loads((D/'sources/Vilin97-lean-pool-head.json').read_text())['sha']
t=json.loads((D/'sources/Vilin97-lean-pool-tree.json').read_text())
if sys.argv[1]=='pool':
 for e in t['tree']:
  p=e['path']
  if p=='projects.yml' or (p.startswith('candidates/') and e['type']=='blob'):
   fetch('https://raw.githubusercontent.com/Vilin97/lean-pool/'+sha+'/'+p,'pool-'+p.replace('/','_'))
else:
 ids=sys.argv[1:]
 rows=json.loads((D/'extracted.json').read_text())
 for i in ids:
  a=rows[i]['source_url'].split('/')[-1]
  q=a+' lean';fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search-'+i+'.json')
  time.sleep(7)
