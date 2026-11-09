import subprocess,json
from pathlib import Path
for n in json.loads(Path("dependencies.json").read_text()):
 print(n,flush=True)
 subprocess.run(["python3","guard.py",n+".lean.log","-o",n+".olean",n+".lean"],check=True)
