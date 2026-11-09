from pathlib import Path
import subprocess,sys
D=Path(__file__).resolve().parents[1]
items=[('arxiv-source.html','https://arxiv.org/abs/math/0303356'),('groups.html','https://arxiv.org/html/math/0304065'),('permutations.html','https://arxiv.org/html/0709.1134'),('springer.html','https://link.springer.com/article/10.1007/s00373-005-0614-3'),('amalgamating.pdf','https://citeseerx.ist.psu.edu/document?doi=14e7aeef20c2583443e4bd042de94af619625eb2&repid=rep1&type=pdf'),('smith.pdf','https://jdhsmith.math.iastate.edu/math/CGDGQG.pdf'),('omega-tree.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/cb0794afb598a762af530e1ebed38deee878e52c?recursive=1')]
for name,url in items:
 subprocess.run(['systemd-run','--user','--scope','-p','MemoryMax=6G',sys.executable,str(D/'scripts/run.py'),'fetch-'+name,sys.executable,str(D/'scripts/fetch.py'),name,url],check=True)
