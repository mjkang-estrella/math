# usage: textify.py LANE_DIR name [maxchars]  -- strip html to text into sources/name.txt
import sys,pathlib,re,html
D=pathlib.Path(sys.argv[1]).resolve()/'sources'; n=sys.argv[2]
b=(D/f'{n}.body').read_bytes().decode('utf8','replace')
b=re.sub(r'(?is)<(script|style).*?</\1>',' ',b); t=html.unescape(re.sub(r'<[^>]+>',' ',b)); t=re.sub(r'[ \t]+',' ',t); t=re.sub(r'\n\s*\n+','\n',t)
(D/f'{n}.txt').write_text(t); print(t[:int(sys.argv[3]) if len(sys.argv)>3 else 3000])
