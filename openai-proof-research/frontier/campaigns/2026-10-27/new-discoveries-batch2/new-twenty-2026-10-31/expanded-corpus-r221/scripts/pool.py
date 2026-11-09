import pathlib,sys,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1];sha=json.loads((D/'sources/pool-head.json').read_text())['sha']
for x in json.loads((D/'sources/pool-tree.json').read_text())['tree']:
 p=x['path']
 if p=='LeanPool/projects.yml' or (p.startswith('candidates/') and x['type']=='blob'):
  get('pool-'+p.replace('/','_'),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+sha+'/'+p)
