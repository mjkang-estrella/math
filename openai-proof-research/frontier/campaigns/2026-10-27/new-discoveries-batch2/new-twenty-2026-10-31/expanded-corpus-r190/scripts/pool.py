import pathlib,json,runpy,sys
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'sources/leanpool-tree.body').read_text());ps=[z['path'] for z in x['tree'] if z['path'].endswith('projects.yml') or z['path'].startswith('candidates/') and z['type']=='blob'];print(ps)
(D/'outputs/pool-paths.json').write_text(json.dumps(ps,indent=2))
args=[]
for n,p in enumerate(ps):args += ['pool-file-'+str(n),'https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/'+p]
sys.argv=[str(D/'scripts/fetch.py')]+args;runpy.run_path(str(D/'scripts/fetch.py'),run_name='__main__')
