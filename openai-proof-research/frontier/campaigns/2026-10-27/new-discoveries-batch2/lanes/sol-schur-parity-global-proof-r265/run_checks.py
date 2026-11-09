from pathlib import Path
import subprocess,json,hashlib,datetime
L=Path(__file__).resolve().parent
# Remove only unused flat source copies accidentally included in the bootstrap.
rows=json.loads((L/'bindings.json').read_text());kept=[]
for r in rows:
 if r['copy'].startswith('frozen/sources/') and not Path(r['copy']).name.startswith(('1904.01925v2.','1609.07639v2.')):
  (L/r['copy']).unlink()
 else:kept.append(r)
(L/'bindings.json').write_text(json.dumps(kept,indent=2)+'\n')
logs=[]
for name in ['mechanisms.py','interval_exchange.py','plateau.py','block_identity.py']:
 p=subprocess.run(['python',str(L/name)],capture_output=True,text=True)
 (L/(name+'.stdout')).write_text(p.stdout);(L/(name+'.stderr')).write_text(p.stderr)
 logs.append(dict(script=name,sha256=hashlib.sha256((L/name).read_bytes()).hexdigest(),exit=p.returncode,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 assert p.returncode==0
(L/'check-runs.json').write_text(json.dumps(logs,indent=2)+'\n');print(json.dumps(logs,indent=2))
