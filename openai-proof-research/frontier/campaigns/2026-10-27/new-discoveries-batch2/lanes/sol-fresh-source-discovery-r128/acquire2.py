from research import fetch
from concurrent.futures import ThreadPoolExecutor
items=[('https://arxiv.org/html/2410.11194v2','sources/partite-v2.html'),('https://arxiv.org/html/2609.12612v1','sources/spectral-public-proof.html'),('https://arxiv.org/abs/2609.12612','sources/spectral-public-versions.html'),('https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2025/80.pdf','sources/domino-companion.pdf')]
with ThreadPoolExecutor(max_workers=3) as e:list(e.map(lambda x:fetch(*x),items))
