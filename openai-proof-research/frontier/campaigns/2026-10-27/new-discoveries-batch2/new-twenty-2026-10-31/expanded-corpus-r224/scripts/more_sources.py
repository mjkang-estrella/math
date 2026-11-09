import pathlib,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch_receipts import get,D,DENIED
DENIED.add('api.github.com')
get('dominion2024','https://www.mdpi.com/2227-7390/12/21/3408')
get('softening2026','https://link.springer.com/article/10.1007/s00332-026-10320-5')
get('poset2026','https://arxiv.org/html/2608.14434')
get('irregular2026','https://arxiv.org/html/2609.09355')
get('locallyinterval-v1','https://arxiv.org/html/2512.19040v1')
