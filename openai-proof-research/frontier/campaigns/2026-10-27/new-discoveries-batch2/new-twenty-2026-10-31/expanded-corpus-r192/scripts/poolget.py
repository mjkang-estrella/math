import pathlib,json,runpy,sys
D=pathlib.Path(__file__).resolve().parents[1];h=json.loads((D/'sources/leanpool-head.body').read_text())['sha'];x=json.loads((D/'sources/leanpool-root.body').read_text());ps=[z['path'] for z in x.get('tree',[]) if z['path'].endswith('projects.yml') or z['path'].startswith('candidates/') and z['type']=='blob'];(D/'outputs/pool-paths.json').write_text(json.dumps(ps,indent=2));args=[]
for n,p in enumerate(ps):args += ['pool-file-'+str(n),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+h+'/'+p]
sys.argv=[str(D/'scripts/fetch.py')]+args;runpy.run_path(sys.argv[0],run_name='__main__')
