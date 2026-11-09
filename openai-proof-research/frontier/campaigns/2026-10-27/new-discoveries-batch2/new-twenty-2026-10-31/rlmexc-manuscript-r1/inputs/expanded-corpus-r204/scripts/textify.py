import sys,re,html,pathlib
s=pathlib.Path(sys.argv[1]).read_text(errors='replace')
s=re.sub(r'<annotation encoding="application/x-tex">(.*?)</annotation>',lambda m:' $'+m.group(1)+'$ ',s,flags=re.S)
s=re.sub(r'<math.*?</math>',lambda m: ' '.join(re.findall(r'\$[^$]*\$',m.group(0))) or '',s,flags=re.S)
s=re.sub(r'<(script|style).*?</\1>','',s,flags=re.S)
s=re.sub(r'<[^>]+>',' ',s); s=html.unescape(s); s=re.sub(r'[ \t]+',' ',s); s=re.sub(r'\n\s*\n+','\n',s)
pathlib.Path(sys.argv[2]).write_text(s)
print(len(s))
