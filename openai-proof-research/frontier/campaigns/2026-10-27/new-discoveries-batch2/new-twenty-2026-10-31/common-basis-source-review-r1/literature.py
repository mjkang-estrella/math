from pathlib import Path
import runpy
L=Path(__file__).resolve().parent;fetch=runpy.run_path(str(L/'fetch.py'))['fetch']
for name,url in [('blasiak.pdf','https://websites.umich.edu/~jblasiak/base-swaps-June2007_submit.pdf'),('bonin.pdf','https://bpb-us-e1.wpmucdn.com/blogs.gwu.edu/dist/3/152/files/2016/04/sparseexchangeweb-11u5hju.pdf'),('regular.html','https://arxiv.org/html/2311.07130'),('workshop.pdf','https://orderandgeometry2016.tcs.uj.edu.pl/docs/OG2016-Problem-Booklet.pdf')]:fetch(name,url)
