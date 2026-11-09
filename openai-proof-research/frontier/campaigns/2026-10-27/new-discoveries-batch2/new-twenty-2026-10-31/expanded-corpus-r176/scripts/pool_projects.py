import sys,pathlib,json
exec((pathlib.Path(__file__).parent/'fetch.py').read_text())
if mode=='poolprojects':
 sha=json.loads((D/'sources/lean-pool-head.json').read_text())['sha'];get(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/projects.yml','lean-pool-projects.yml')
 tree=json.loads((D/'sources/lean-pool-tree.json').read_text());paths=[x['path'] for x in tree['tree'] if x['type']=='blob' and ('projects' in x['path'].lower()) and x['path'].endswith(('.yml','.yaml'))];print(paths)
 for j,p in enumerate(paths):get(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}',f'lean-pool-projects-actual-{j}.yml')
