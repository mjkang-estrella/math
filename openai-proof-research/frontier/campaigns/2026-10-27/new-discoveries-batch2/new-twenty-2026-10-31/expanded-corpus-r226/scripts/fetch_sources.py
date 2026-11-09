from pathlib import Path
import json,subprocess,sys
L=Path(__file__).resolve().parents[1]; rows=json.loads((L/'reservation.json').read_text())['rows']
urls=list(dict.fromkeys(r['source_url'] for r in rows))
subprocess.run([sys.executable,'-I','-B',str(L/'scripts/fetch.py')]+urls,check=True)
