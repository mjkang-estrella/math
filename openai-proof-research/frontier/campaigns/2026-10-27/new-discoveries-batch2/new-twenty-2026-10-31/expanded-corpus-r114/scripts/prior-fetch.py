import sys,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).parent))
from fetch import get
for item in [('prior-2607.22874-abs.html','https://arxiv.org/abs/2607.22874'),('prior-2607.22874.html','https://arxiv.org/html/2607.22874'),('prior-2605.07196-abs.html','https://arxiv.org/abs/2605.07196'),('2508.01163-abs.html','https://arxiv.org/abs/2508.01163')]:
    print(get(item),flush=True)
