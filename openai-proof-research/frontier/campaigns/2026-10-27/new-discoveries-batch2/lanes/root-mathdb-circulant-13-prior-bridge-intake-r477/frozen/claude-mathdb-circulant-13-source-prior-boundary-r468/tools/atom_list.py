"""List entries of a saved arXiv Atom response: id, published, title, authors, journal_ref.
usage: atom_list.py BODY OUT.json"""
import json, sys, xml.etree.ElementTree as ET

ns = {'a': 'http://www.w3.org/2005/Atom', 'x': 'http://arxiv.org/schemas/atom',
      'o': 'http://a9.com/-/spec/opensearch/1.1/'}
t = ET.parse(sys.argv[1]).getroot()
out = {'totalResults': t.findtext('o:totalResults', namespaces=ns), 'entries': []}
for e in t.findall('a:entry', ns):
    out['entries'].append({
        'id': (e.findtext('a:id', namespaces=ns) or '').strip(),
        'published': e.findtext('a:published', namespaces=ns),
        'title': ' '.join((e.findtext('a:title', namespaces=ns) or '').split()),
        'authors': [a.findtext('a:name', namespaces=ns) for a in e.findall('a:author', ns)],
        'journal_ref': e.findtext('x:journal_ref', namespaces=ns),
        'summary': ' '.join((e.findtext('a:summary', namespaces=ns) or '').split()),
    })
json.dump(out, open(sys.argv[2], 'w'), indent=1, ensure_ascii=False)
print(out['totalResults'], len(out['entries']))
for x in out['entries']:
    print(x['published'][:10], x['id'].rsplit('/', 1)[-1], '|', x['title'][:110], '|', '; '.join(x['authors'])[:70])
