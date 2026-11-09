import pathlib,json,sys,runpy
D=pathlib.Path(__file__).resolve().parents[1]
a=json.loads((D/'reservation.json').read_text())['rows']; start=int(sys.argv[1]); end=int(sys.argv[2]); args=[]
for x in a[start:end]:args += [str(x['mathdb_id'])+'-abs',x['source_url']]
sys.argv=[str(D/'scripts/fetch.py')]+args
runpy.run_path(str(D/'scripts/fetch.py'),run_name='__main__')
