import pathlib,json,re,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];urls=[];rows=[]
for p in sorted((D/'sources').glob('*/receipt.json')):
 r=json.loads(p.read_text())
 if '/abs/' not in r['url'] or r.get('status')!=200:continue
 s=(p.parent/'body').read_text();links=re.findall(r'href="(https://doi.org/[^\"]+)"',s);links=[x for x in links if '10.48550' not in x]
 rows.append({'arxiv':r['url'],'doi_links':links,'receipt':str(p.relative_to(D))})
 urls+=links
(D/'outputs/version-of-record-routes.json').write_text(json.dumps(rows,indent=2))
# Never retry a denied route, including through redirects.
known={json.loads(p.read_text())['url'] for p in (D/'sources').glob('*/receipt.json')}
urls=[u for u in dict.fromkeys(urls) if u not in known]
subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*urls],check=True)
