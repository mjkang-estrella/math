import sys,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import attack
print(json.dumps(attack.run(Path(__file__).resolve().parents[3]),sort_keys=True,indent=2))
