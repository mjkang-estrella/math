import pathlib,subprocess,xml.etree.ElementTree as E,sys
L=pathlib.Path(__file__).parent
for name in sys.argv[1:]:
 if name.endswith('.xml'):
  n={'a':'http://www.w3.org/2005/Atom'};root=E.parse(L/'frozen'/name)
  for e in root.findall('a:entry',n):
   print('\n',e.findtext('a:id',namespaces=n),e.findtext('a:title',namespaces=n),e.findtext('a:published',namespaces=n),e.findtext('a:updated',namespaces=n));print(e.findtext('a:summary',namespaces=n))
 else:
  p=L/'frozen'/name;q=L/(name+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);print(q.read_text()[:65000])
