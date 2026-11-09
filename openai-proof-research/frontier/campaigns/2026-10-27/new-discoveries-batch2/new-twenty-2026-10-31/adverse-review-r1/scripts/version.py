from pathlib import Path
import sys,hashlib,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
from run import run,BIN,PKG,R
assert run('version',[str(BIN/'lean'),'--version'])==0
head=(PKG/'mathlib/.git/HEAD').read_text().strip()
if head.startswith('ref: '):head=(PKG/'mathlib/.git'/head[5:]).read_text().strip()
assert head=='d13f23b723b8a846827a245b89c10fc7d3f11612'
(R/'receipts/dependencies.json').write_text(json.dumps(dict(mathlib=head,lean_sha256=hashlib.sha256((BIN/'lean').read_bytes()).hexdigest(),version=(R/'logs/version.log').read_text()),indent=2))
