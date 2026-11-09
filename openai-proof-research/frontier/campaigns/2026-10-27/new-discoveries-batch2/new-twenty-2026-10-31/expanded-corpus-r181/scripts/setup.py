from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parents[1]; B=D.parent.parent
for p in [B/'ledger.json',D.parent/'ledger.json',B/'prior-campaign-context.json']:
 if p.exists():
  b=p.read_bytes(); (D/'outputs'/('context-'+p.parent.name+'-'+p.name)).write_bytes(b)
  o=json.loads(b); print(str(p),str(o)[:18000])
