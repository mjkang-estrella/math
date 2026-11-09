import pathlib,sys,re,json,runpy,html
D=pathlib.Path(sys.argv[1]).resolve();sys.argv=sys.argv[:2];fetch=runpy.run_path(str(D/'scripts/fetch.py'))['fetch']
t=(D/'sources/grundy-refutation/body').read_text();links=list(dict.fromkeys(html.unescape(s) for s in re.findall(r'href="([^"]+)"',t) if any(x in s.lower() for x in ['pdf','source','download','github'])))
print(links)
(D/'outputs/grundy-links.json').write_text(json.dumps(links,indent=2))
for j,s in enumerate(links):
 if 'pdf' in s:fetch(s if s.startswith('http') else 'https://hexagonmath.org'+s,'grundy-body-'+str(j))
