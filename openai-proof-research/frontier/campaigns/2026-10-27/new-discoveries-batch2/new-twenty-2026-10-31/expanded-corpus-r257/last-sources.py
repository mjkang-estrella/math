exec(compile((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('with concurrent.futures.ThreadPoolExecutor')[0],str(__file__),'exec'))
jobs=[('regular-refutation.pdf','https://www.math.tau.ac.il/~nogaa/PDFS/nice3.pdf'),('path-later.pdf','https://arxiv.org/pdf/2506.19100'),('regular-journal.html','https://doi.org/10.1007/s00373-024-02774-9')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,jobs):print(r,flush=True)
