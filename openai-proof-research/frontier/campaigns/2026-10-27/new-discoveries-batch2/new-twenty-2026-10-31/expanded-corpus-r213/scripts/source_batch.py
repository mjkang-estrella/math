import pathlib,json,subprocess,sys
L=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((L/'reservation.json').read_text())
urls=[x['source_url'] for x in r['rows']]
subprocess.run([sys.executable,'-I',str(L/'scripts/http.py'),*urls],check=True)
