import re
urls=set()
for name in json.loads((P/'historical-results-allowlist.json').read_text()):
 if any(s in name for s in ['crown-vnumber-','crim-conway-source-qualification-r1']):continue
 f=pathlib.Path(name)
 if not f.is_file():continue
 for url in re.findall(r'https[^\s"<>]+',f.read_text()):
  if any(s in url.lower() for s in ['leanpool','openai/math','projects.yml','raw.githubusercontent.com']):urls.add(url)
print('\n'.join(sorted(urls)[:70]))
