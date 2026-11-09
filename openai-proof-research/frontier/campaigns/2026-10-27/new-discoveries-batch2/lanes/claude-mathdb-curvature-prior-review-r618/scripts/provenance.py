"""Build source-provenance.json from fetch-log.tsv plus version facts read from abs pages.
Usage (lane dir): python3 -I -B scripts/provenance.py"""
import json
rows = [l.rstrip('\n').split('\t') for l in open('fetch-log.tsv') if l.strip()]
fetches = [{'utc': r[0], 'kind': r[1], 'url': r[2], 'http': r[3], 'size': int(r[-2]), 'sha256': r[-1],
            'effective_url': r[4] if len(r) == 7 else ''} for r in rows]
out = {
 'headers': "generic: User-Agent 'Mozilla/5.0 (X11; Linux x86_64)', Accept */*; no identity, cookies or credentials",
 'fetches': fetches,
 'sources': {
  'BRT': {'arxiv': '1802.01952v2', 'versions': {'v1': '2018-02-06T14:10:24Z', 'v2': '2019-10-13T19:15:38Z'}, 'latest_on_abs_page': 'v2',
          'journal': {'venue': 'International Mathematics Research Notices', 'year': 2021, 'issue': 22, 'pages': '17091-17139', 'doi': '10.1093/imrn/rnz305', 'online': '2019-12-09', 'body_read': False},
          'cached_r602_pdf_identical': True},
  'BLY': {'arxiv': '2103.00941v2', 'versions': {'v1': '2021-03-01T12:08:27Z', 'v2': '2021-05-10T14:16:36Z'}, 'latest_on_abs_page': 'v2',
          'journal': {'venue': 'Asian Journal of Mathematics', 'volume': 25, 'issue': 6, 'year': 2021, 'doi': '10.4310/ajm.2021.v25.n6.a1', 'body_read': False},
          'cached_r602_pdf_identical': True}},
 'derived': 'see derived-bindings.tsv (hashed before reading)'}
json.dump(out, open('source-provenance.json', 'w'), indent=1)
print(len(fetches))
