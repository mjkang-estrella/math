import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];rows=[]
for p in (D/'sources').glob('*.html'):
 text=p.read_text();rows.append({'file':p.name,'bytes':p.stat().st_size,'has_article':bool(re.search('ltx_document|ltx_page_content',text)),'unavailable':bool(re.search('not available|not yet supported|No HTML|Conversion Error',text,re.I))})
(D/'outputs/html-availability.json').write_text(json.dumps(rows,indent=2))
for r in rows:
 if not r['has_article']:print(r)
