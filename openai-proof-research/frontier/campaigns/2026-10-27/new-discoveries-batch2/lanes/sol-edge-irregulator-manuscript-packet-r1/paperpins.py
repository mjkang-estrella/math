from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent;tool=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/t088p133-manuscript-r2/tools/tectonic')
files=[tool]+[p for p in (Path.home()/'.cache/tectonic').rglob('*') if p.is_file()]
d={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(L/'packet/paper-pins.json').write_text(json.dumps(d,indent=2)+'\n');print('paper pin count',len(d))
