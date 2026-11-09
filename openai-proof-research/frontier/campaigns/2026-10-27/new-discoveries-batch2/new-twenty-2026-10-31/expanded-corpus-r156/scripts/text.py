import pathlib,re,html
for p in pathlib.Path('sources').glob('*.html'):
 s=p.read_text(errors='replace');s=re.sub(r'<(script|style|nav|footer)\b.*?</\1>','',s,flags=re.S)
 s=re.sub(r'<math\b[^>]*alttext="([^"]*)".*?</math>',lambda m:html.unescape(m[1]),s,flags=re.S)
 s=re.sub(r'</(?:p|h[1-6]|div|section|li)>','\n',s);s=re.sub('<[^>]*>','',s);s=html.unescape(s)
 s=re.sub(r'[ \t]+',' ',s);s=re.sub(r'\n\s*\n','\n',s)
 p.with_suffix('.txt').write_text(s)
