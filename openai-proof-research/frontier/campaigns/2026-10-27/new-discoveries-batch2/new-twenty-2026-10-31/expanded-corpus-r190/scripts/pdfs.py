import pathlib,json,runpy,sys
D=pathlib.Path(__file__).resolve().parents[1];a=list(json.loads((D/'outputs/versions.json').read_text()).items());args=[]
for i,x in a[int(sys.argv[1]):int(sys.argv[2])]:
 for v in x['versions']:args += [i+'-v'+v,'https://arxiv.org/pdf/'+x['arxiv']+'v'+v]
sys.argv=[str(D/'scripts/fetch.py')]+args;runpy.run_path(str(D/'scripts/fetch.py'),run_name='__main__')
