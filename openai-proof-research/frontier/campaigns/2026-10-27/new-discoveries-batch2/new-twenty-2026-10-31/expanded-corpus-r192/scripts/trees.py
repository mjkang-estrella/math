import pathlib,json,runpy,sys
D=pathlib.Path(__file__).resolve().parents[1];args=[]
for name,repo in [('leanpool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 x=json.loads((D/f'sources/{name}-head.body').read_text());sha=x['sha'];print(name,sha)
 args += [name+'-root','https://api.github.com/repos/'+repo+'/git/trees/'+sha+('?recursive=1' if name=='leanpool' else '')]
sys.argv=[str(D/'scripts/fetch.py')]+args;runpy.run_path(sys.argv[0],run_name='__main__')
