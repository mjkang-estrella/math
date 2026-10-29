from research import fetch
from concurrent.futures import ThreadPoolExecutor
items=[('https://arxiv.org/html/2501.17765v1','sources/domino.html'),('https://arxiv.org/html/2410.11194v1','sources/partite.html'),('https://arxiv.org/abs/2501.17765','sources/domino-versions.html'),('https://arxiv.org/abs/2410.11194','sources/partite-versions.html'),('https://www.ibs.re.kr/ecopro/wp-content/uploads/2025/12/Communications-in-Combinatorics-pamphlet-20251212-15.pdf','sources/spectral.pdf')]
with ThreadPoolExecutor(max_workers=3) as ex:list(ex.map(lambda x:fetch(*x),items))
