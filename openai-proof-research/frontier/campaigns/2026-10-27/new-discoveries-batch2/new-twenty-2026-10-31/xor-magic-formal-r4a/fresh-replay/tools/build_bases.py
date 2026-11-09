from pathlib import Path
import subprocess,json
p=Path(__file__).resolve().parent.parent
for module in json.loads((p/'modules.json').read_text())[2:]:
 print(module,flush=True)
 code=subprocess.call(['bash',str(p/'compile.sh'),f'logs/{module}.log','-o',f'formal/{module}.olean',f'formal/{module}.lean'])
 if code: raise SystemExit(code)
