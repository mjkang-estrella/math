import pathlib,runpy,sys,json
D=pathlib.Path(__file__).resolve().parents[1]; get=runpy.run_path(str(D/'scripts/fetch.py'))['get']
items=[('2410.11818.html','https://arxiv.org/html/2410.11818'),('2510.04993.html','https://arxiv.org/html/2510.04993'),('2309.10203.html','https://arxiv.org/html/2309.10203'),('2204.12433.html','https://arxiv.org/html/2204.12433'),('2304.10134.html','https://arxiv.org/html/2304.10134'),('2201.00721.html','https://arxiv.org/html/2201.00721'),('2212.05398.pdf','https://arxiv.org/pdf/2212.05398'),('2107.09699.pdf','https://arxiv.org/pdf/2107.09699')]
for x in items:print(get(x),flush=True)
head=json.loads((D/'sources/omega-head.json').read_text())['sha'];print(get(('omega-tree.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{head}?recursive=1')),flush=True)
