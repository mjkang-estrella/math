from work import *
import urllib.parse,xml.etree.ElementTree as E
qs={'fractal':'au:Alpan AND (all:Widom OR all:Szego OR all:Green)','helly':'all:Swanepoel AND (all:symmetry OR all:Helly)','valent':'all:Valent AND all:type','santalo':'all:Santalo AND (all:Kalantzopoulos OR all:Saroglou)'}
for name,q in qs.items():
 p=fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=25&sortBy=submittedDate&sortOrder=descending',name+'-prior.xml');freeze(p)
 for e in E.parse(p).findall('{http://www.w3.org/2005/Atom}entry'):
  print(name,e.findtext('{http://www.w3.org/2005/Atom}id'),e.findtext('{http://www.w3.org/2005/Atom}title'),e.findtext('{http://www.w3.org/2005/Atom}summary')[:900])
for a in ['2409.03664v3']:
 p=fetch('https://arxiv.org/pdf/'+a,a+'.pdf');q=freeze(p);subprocess.run(['pdftotext','-layout',str(q),str(L/'science'/(a+'.txt'))],check=True)
