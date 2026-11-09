import sys,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).parent))
from fetch import get
for item in [('prior-2512.12251-abs.html','https://arxiv.org/abs/2512.12251'),('2505.06486-abs.html','https://arxiv.org/abs/2505.06486')]:
    print(get(item),flush=True)
