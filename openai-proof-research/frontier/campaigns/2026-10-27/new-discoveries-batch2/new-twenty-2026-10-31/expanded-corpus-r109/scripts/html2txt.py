import re,sys,html,pathlib
# Convert arXiv HTML to text, keeping LaTeX alttext of math elements.
def conv(s):
    s=re.sub(r'<math[^>]*?alttext="([^"]*)"[^>]*>.*?</math>',lambda m:' $'+html.unescape(m.group(1))+'$ ',s,flags=re.S)
    s=re.sub(r'<(script|style)[^>]*>.*?</\1>','',s,flags=re.S)
    s=re.sub(r'<br\s*/?>|</p>|</div>|</h\d>|</li>|</tr>','\n',s)
    s=re.sub(r'<[^>]+>','',s)
    s=html.unescape(s)
    s=re.sub(r'[ \t]+',' ',s); s=re.sub(r'\n\s*\n+','\n\n',s)
    return s
for p in sys.argv[1:]:
    p=pathlib.Path(p); pathlib.Path(str(p)[:-5]+'.txt').write_text(conv(p.read_text(errors='replace')))
