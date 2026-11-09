exec(compile((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('with concurrent.futures.ThreadPoolExecutor')[0],str(__file__),'exec'))
jobs=json.loads((L/'version-jobs.json').read_text())+[(n,u) for n,u in [('formation-later.pdf','https://math.colgate.edu/~integers/w111/w111.pdf'),('cluster-later.pdf','https://arxiv.org/pdf/1809.05116'),('electrical-later.pdf','https://plhersh.math.ncsu.edu/shell-electrical.pdf'),('cross-journal.html','https://doi.org/10.1016/j.jnt.2013.09.006')]]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,jobs):print(r,flush=True)
