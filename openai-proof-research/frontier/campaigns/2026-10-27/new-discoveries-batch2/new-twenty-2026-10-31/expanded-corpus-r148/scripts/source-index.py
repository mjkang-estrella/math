import pathlib,json,re,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1];idx={}
for row in json.loads((L/'reservation.json').read_text())['rows']:
 a=row['source_url'].split('/')[-1];b=(L/f'sources/{a}.abs').read_text();versions=re.findall(r'\[v(\d+)\]',b);meta=re.search(r'<meta property="og:url" content="([^"]+)',b)
 idx[str(row['mathdb_id'])]={'arxiv':a,'current_version_url':meta.group(1) if meta else None,'listed_versions':sorted(set(versions),key=int),'pdf_receipt':json.loads((L/f'sources/{a}.pdf.receipt.json').read_text()),'abs_receipt':json.loads((L/f'sources/{a}.abs.receipt.json').read_text())}
(L/'outputs/source-index.json').write_text(json.dumps(idx,indent=2))
for i,v in idx.items():print(i,v['current_version_url'])
