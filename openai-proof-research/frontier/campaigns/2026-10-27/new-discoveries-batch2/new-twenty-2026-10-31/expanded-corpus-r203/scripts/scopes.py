import sys,pathlib,json
sys.path.insert(0,str(pathlib.Path(sys.argv[1])/'scripts'));from fetch import fetch
D=pathlib.Path(sys.argv[1])
for repo,label,path in [('openai/math','openai','preprints'),('the-omega-institute/trureturing','omega','Problems')]:
 sha=json.loads((D/'sources'/(repo.replace('/','-')+'-head')/'body').read_text())['sha'];root=fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha,label+'-root-nonrecursive')
 if root:
  entry=next((x for x in root['tree'] if x['path']==path),None)
  if entry:fetch('https://api.github.com/repos/'+repo+'/git/trees/'+entry['sha']+'?recursive=1',label+'-'+path+'-complete')
