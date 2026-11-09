import sys,runpy
from pathlib import Path
L=Path(__file__).resolve().parent
jobs=[('fetch','plantri58.tar.gz','https://users.cecs.anu.edu.au/~bdm/plantri/plantri58.tar.gz'),('fetch','fullgen-guide.txt','https://users.cecs.anu.edu.au/~bdm/plantri/fullgen-guide.txt'),('fetch','cospectral-search.html','https://arxiv.org/search/?query=fullerene+cospectral&searchtype=all&abstracts=show&size=50'),('fetch','pencil-search.html','https://arxiv.org/search/?query=generalized+characteristic+polynomial+switching&searchtype=all&abstracts=show&size=50'),('fetch','successor-search.html','https://arxiv.org/search/?query=%222410.19322%22&searchtype=all&abstracts=show&size=50')]
for job in jobs:
 sys.argv=[str(L/'work.py'),*job];runpy.run_path(str(L/'work.py'),run_name='__main__')
