import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
for r in ['pool','omega','openai']:
 x=json.loads((D/f'sources/{r}-head.body').read_text());print(r,x['sha'])
tree=json.loads((D/'sources/pool-tree.body').read_text())
p=[x['path'] for x in tree['tree'] if x['path'].startswith('candidates/') or 'projects.y' in x['path']];print('pool paths',p[:15],len(p));(D/'outputs/pool-paths.json').write_text(json.dumps(p))
args=[]
for n,p in enumerate(p):
 if not p.endswith(('.yml','.yaml','.md','.json','.lean')):continue
 args += ['pool-file-'+str(n),'https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/'+p]
subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*args])
