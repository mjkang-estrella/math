import pathlib,re,html
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 s=p.read_text();s=re.sub(r'<math\b[^>]*alttext="([^"]*)"[^>]*>.*?</math>',lambda m: html.unescape(m[1]),s,flags=re.S);s=re.sub(r'<(script|style)\b.*?</\1>','',s,flags=re.S);s=re.sub('<[^>]+>',' ',s);s=html.unescape(s);s=re.sub(r'\s+',' ',s)
 p.with_suffix('.txt').write_text(s)
 # contexts rather than claiming whole proof-body reading
 if p.name.endswith('body.html'):
  ctx=[]
  for m in re.finditer(r'conjectur|verified|computer|exhaust|[Tt]heorem|[Pp]roposition',s):ctx.append(s[max(0,m.start()-100):m.start()+1300])
  (D/'outputs'/(p.stem+'-contexts.txt')).write_text('\n\n'.join(ctx))
