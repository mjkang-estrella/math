import re,sys,html,pathlib
# Math alttext is unescaped only after tag stripping (so '<' inside formulas survives).
for f in sys.argv[1:]:
  t=pathlib.Path(f).read_text(errors='replace')
  t=re.sub(r'<head>.*?</head>','',t,flags=re.S)
  t=re.sub(r'<math[^>]*alttext="([^"]*)"[^>]*>.*?</math>',lambda m:' $'+m.group(1)+'$ ',t,flags=re.S)
  t=re.sub(r'<(script|style)[^>]*>.*?</\1>','',t,flags=re.S)
  t=re.sub(r'</(p|div|h\d|li|tr|section)>','\n',t)
  t=re.sub(r'<[^>]+>','',t); t=html.unescape(t)
  t=re.sub(r'[ \t]+',' ',t); t=re.sub(r'\n\s*\n+','\n',t)
  out=re.sub(r'\.(html\.)?html$','',f)+'.body.txt' if not f.endswith('.abs.html') else None
  if out: pathlib.Path(out).write_text(t); print(out,len(t))
