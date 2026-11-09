from pathlib import Path
import urllib.request,urllib.parse,hashlib,json,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent
url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':'all:"slender" AND all:"regular"','max_results':8})
try:
 with urllib.request.urlopen(url,timeout=30) as r:data=r.read(1000000)
 p=L/'thin-search.xml';p.write_bytes(data)
 print('sha256',hashlib.sha256(data).hexdigest())
 for x in E.fromstring(data).findall('{http://www.w3.org/2005/Atom}entry'):
  print(x.findtext('{http://www.w3.org/2005/Atom}id'),x.findtext('{http://www.w3.org/2005/Atom}title'))
except Exception as e:
 (L/'thin-search-failure.txt').write_text(repr(e)+'; no retry');print(repr(e))
