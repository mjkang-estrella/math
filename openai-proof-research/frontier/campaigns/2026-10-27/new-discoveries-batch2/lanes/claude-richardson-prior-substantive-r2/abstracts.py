import json, sys
# Decode OpenAlex inverted abstracts: abstracts.py FILE
d = json.load(open(sys.argv[1]))
print('count', d['meta']['count'])
for w in d['results']:
    inv = w.get('abstract_inverted_index') or {}
    pos = sorted((p, t) for t, ps in inv.items() for p in ps)
    ab = ' '.join(t for _, t in pos)
    oa = (w.get('best_oa_location') or {}) or {}
    print('##', w.get('publication_year'), w.get('title'))
    print('   ids:', w.get('ids', {}).get('doi'), '| oa:', oa.get('pdf_url') or oa.get('landing_page_url'))
    print('   ', ab[:700])
