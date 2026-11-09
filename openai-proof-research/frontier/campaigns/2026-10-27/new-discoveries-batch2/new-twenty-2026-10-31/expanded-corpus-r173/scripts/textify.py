import pathlib,re,html
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 t=p.read_text();t=re.sub(r'<math\b([^>]*)>.*?</math>',lambda m:html.escape(html.unescape(re.search(r'alttext="([^"]*)"',m[1])[1])) if re.search(r'alttext="([^"]*)"',m[1]) else '',t,flags=re.S)
 t=re.sub(r'<(script|style)\b.*?</\1>','',t,flags=re.S);t=html.unescape(re.sub('<[^>]+>',' ',t));t=re.sub(r'\s+',' ',t)
 p.with_suffix('.txt').write_text(t)
 if '-abs' in p.name:print(p.stem,re.findall(r'\[v\d+\].{0,100}',t))
