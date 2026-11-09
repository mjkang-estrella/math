from fetch import get
import json
from pathlib import Path
p=Path(__file__).resolve().parents[1]
o=json.loads((p/'sources/omega-head.json').read_text())
for item in [('omega-tree.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+o['commit']['tree']['sha']+'?recursive=1'),('2501.01112.html','https://arxiv.org/html/2501.01112'),('2610.25381.html','https://arxiv.org/html/2610.25381')]:print(get(item),flush=True)
