import pathlib,json,subprocess,sys
L=pathlib.Path(__file__).resolve().parents[1]
for row in json.loads((L/'reservation.json').read_text())['rows']:
 a=row['source_url'].rsplit('/',1)[1]
 subprocess.run([sys.executable,'-I',str(L/'scripts/http.py'),'https://arxiv.org/pdf/'+a],check=True)
