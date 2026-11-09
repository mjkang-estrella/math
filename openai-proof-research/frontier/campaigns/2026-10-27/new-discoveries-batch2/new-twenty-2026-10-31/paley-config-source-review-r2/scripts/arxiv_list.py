"""List entries from an arXiv API Atom file. Usage: python3 -I arxiv_list.py FILE"""
import sys, xml.etree.ElementTree as ET
ns = {"a": "http://www.w3.org/2005/Atom"}
r = ET.parse(sys.argv[1]).getroot()
for e in r.findall("a:entry", ns):
    t = " ".join(e.find("a:title", ns).text.split()); i = e.find("a:id", ns).text.rsplit("/", 1)[-1]
    au = ", ".join(a.find("a:name", ns).text for a in e.findall("a:author", ns))
    print(i, e.find("a:published", ns).text[:10], "|", t, "|", au[:90])
