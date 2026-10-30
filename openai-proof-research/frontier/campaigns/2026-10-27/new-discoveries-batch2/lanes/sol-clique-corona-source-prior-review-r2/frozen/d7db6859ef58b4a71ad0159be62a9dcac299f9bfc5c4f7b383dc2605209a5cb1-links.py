import pathlib,re
L=pathlib.Path(__file__).parent
t=(L/'survey-index.html').read_text()
for m in re.finditer('corona|Mandrescu|Levit',t,re.I):print(re.sub('<[^>]+>',' ',t[max(0,m.start()-600):m.end()+1800]))
for m in re.finditer(r'<a\b[^>]*href=[\"\x27]([^\"\x27]+)[\"\x27][^>]*>(.*?)</a>',t,re.S|re.I):
 if any(w in (m[1]+' '+m[2]).lower() for w in ['corona','levit','mandrescu','.pdf']):print(m[1], re.sub('<[^>]+>','',m[2]).strip())
