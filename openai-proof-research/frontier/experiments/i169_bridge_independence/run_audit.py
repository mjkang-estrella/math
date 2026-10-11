import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import audit,json
print(json.dumps(audit.run(Path(__file__).resolve().parents[3]),sort_keys=True,indent=2))
