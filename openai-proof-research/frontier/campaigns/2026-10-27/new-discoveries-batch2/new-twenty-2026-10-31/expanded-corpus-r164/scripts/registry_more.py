import pathlib,json,urllib.parse,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
exec(compile((D/'scripts/fetch.py').read_text().split("if __name__")[0],str(D/'scripts/fetch.py'),'exec'))
if sys.argv[1]=='trees':
 sha=json.loads((D/'sources/Vilin97-lean-pool-head.json').read_text())['sha'];fetch('https://raw.githubusercontent.com/Vilin97/lean-pool/'+sha+'/LeanPool/projects.yml','pool-projects.yml')
 for repo,scope in [('the-omega-institute/trureturing','D5'),('the-omega-institute/trureturing','Problems'),('openai/math','preprints')]:
  tag=repo.replace('/','-');head=json.loads((D/'sources'/(tag+'-head.json')).read_text())['sha']
  fetch('https://api.github.com/repos/'+repo+'/git/trees/'+head+':'+scope+'?recursive=1',tag+'-'+scope+'.json')
else:
 for i,q in [('333364','"counterfeit coins" lean'),('337410','"multipartite Ramsey" lean'),('332342','"universal partial words" lean'),('337293','"set sequential" lean'),('337830','"packing edge" lean'),('333709','"percolation" "projective" lean')]:
  fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-name-'+i+'.json');time.sleep(7)
