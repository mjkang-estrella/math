from pathlib import Path
import urllib.request,urllib.error,json,datetime,hashlib,concurrent.futures
L=Path(__file__).parent;P=L/'primary'
s=(L/'fetch.py').read_text();exec(s[s.index('def fetch('):s.index('with concurrent.futures.ThreadPoolExecutor')])
urls={'ims90':'https://www.math.stonybrook.edu/preprintsearch?search=ims90-01','ims92':'https://www.math.stonybrook.edu/preprintsearch?search=ims92-07','ericksonindex':'https://jeffe.cs.illinois.edu/open/','equiprojective-successor':'https://arxiv.org/pdf/1009.2252v1'}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
 for x in ex.map(fetch,urls.items()):print(x)
