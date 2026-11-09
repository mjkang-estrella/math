from pathlib import Path
import urllib.request,urllib.error,json,datetime,hashlib,concurrent.futures
L=Path(__file__).parent;P=L/'primary'
s=(L/'fetch.py').read_text();exec(s[s.index('def fetch('):s.index('with concurrent.futures.ThreadPoolExecutor')])
urls={'holomorphic92':'https://www.math.stonybrook.edu/preprints/ims92-7.pdf','conformal90':'https://www.math.stonybrook.edu/preprints/ims90-1.pdf','skeleton':'https://jeffe.cs.illinois.edu/open/skeleton.html','motorcycles':'https://jeffe.cs.illinois.edu/open/cycles.html','klee':'https://jeffe.cs.illinois.edu/open/klee.html'}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
 for x in ex.map(fetch,urls.items()):print(x)
