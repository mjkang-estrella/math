import sys,xml.etree.ElementTree as ET
ns={'a':'http://www.w3.org/2005/Atom'}
t=ET.parse(sys.argv[1]); o=open(sys.argv[2],'w',encoding='utf-8')
for e in t.getroot().findall('a:entry',ns):
    g=lambda k:(e.find('a:'+k,ns).text or '').strip() if e.find('a:'+k,ns) is not None else ''
    au=', '.join(a.find('a:name',ns).text for a in e.findall('a:author',ns))
    o.write('== %s | pub %s | upd %s\nTITLE: %s\nAUTH: %s\nABS: %s\n\n'%(g('id'),g('published'),g('updated'),' '.join(g('title').split()),au,' '.join(g('summary').split())))
