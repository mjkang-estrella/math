# Render arXiv Atom API XML (bound input) to a text view: id, version, published/updated, title, journal_ref, comment, abstract.
import sys,xml.etree.ElementTree as ET
A='{http://www.w3.org/2005/Atom}'; X='{http://arxiv.org/schemas/atom}'
t=ET.parse(sys.argv[1]).getroot(); out=open(sys.argv[2],'w',encoding='utf-8')
for e in t.findall(A+'entry'):
    g=lambda k,ns=A:(e.findtext(ns+k) or '').strip().replace('\n',' ')
    out.write('### %s | pub %s | upd %s\nTITLE: %s\nJREF: %s | DOI: %s | COMMENT: %s\nABS: %s\n\n'%(g('id'),g('published'),g('updated'),' '.join(g('title').split()),g('journal_ref',X),g('doi',X),g('comment',X),' '.join(g('summary').split())))
