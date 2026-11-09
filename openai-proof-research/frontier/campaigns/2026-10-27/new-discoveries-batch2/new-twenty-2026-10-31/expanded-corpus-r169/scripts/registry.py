exec(compile((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split("if sys.argv[1]=='sources':")[0],str(__import__('pathlib').Path(__file__).parent/'fetch.py'),'exec'))
import time
sha=json.loads((D/'sources/pool-head.json').read_text())['sha']
paths=[x['path'] for x in json.loads((D/'sources/pool-tree.json').read_text())['tree'] if x['type']=='blob' and (x['path'].startswith('candidates/') or x['path']=='LeanPool/projects.yml')]
for p in paths:fetch('https://raw.githubusercontent.com/Vilin97/lean-pool/'+sha+'/'+p,'pool-'+p.replace('/','_'))
