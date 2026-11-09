import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
args=[]
for row in json.loads((D/'reservation.json').read_text())['rows']:
 i=row['mathdb_id'];args += [str(i)+'-abs',row['source_url']]
subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*args],check=True)
