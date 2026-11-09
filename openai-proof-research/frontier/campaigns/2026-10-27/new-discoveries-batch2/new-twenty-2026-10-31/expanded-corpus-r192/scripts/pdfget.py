import pathlib,json,re,sys,runpy
D=pathlib.Path(__file__).resolve().parents[1];a=json.loads((D/'reservation.json').read_text())['rows'];args=[]
for x in a[int(sys.argv[1]):int(sys.argv[2])]:
 s=(D/f"sources/{x['mathdb_id']}-abs.body").read_text(); vs=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int)
 for v in vs:args += [str(x['mathdb_id'])+'-v'+v,x['source_url'].replace('/abs/','/pdf/')+'v'+v]
sys.argv=[str(D/'scripts/fetch.py')]+args;runpy.run_path(sys.argv[0],run_name='__main__')
