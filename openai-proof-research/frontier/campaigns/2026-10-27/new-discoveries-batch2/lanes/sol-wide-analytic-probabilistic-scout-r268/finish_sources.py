from work import *
from read_sources import ids
import xml.etree.ElementTree as E
p=fetch('https://arxiv.org/pdf/1712.03571v3','1712.03571v3.pdf');q=freeze(p);subprocess.run(['pdftotext','-layout',str(q),str(L/'science/1712.03571v3.txt')],check=True)
p=fetch('https://export.arxiv.org/api/query?id_list='+','.join(ids+['2409.03664v3','1808.05936v2','2608.17321v1','1712.03571v3'])+'&max_results=25','versions.xml');freeze(p)
ns='{http://www.w3.org/2005/Atom}';out=[]
for e in E.parse(p).findall(ns+'entry'):
 out.append(dict(id=e.findtext(ns+'id'),title=e.findtext(ns+'title'),published=e.findtext(ns+'published'),updated=e.findtext(ns+'updated'),authors=[a.findtext(ns+'name') for a in e.findall(ns+'author')]))
save(L/'chronology.json',out)
print(json.dumps(out,indent=2)[:12000])
