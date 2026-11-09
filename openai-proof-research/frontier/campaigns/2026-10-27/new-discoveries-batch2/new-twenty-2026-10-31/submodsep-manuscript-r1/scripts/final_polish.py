from pathlib import Path
L=Path(__file__).resolve().parents[1]
p=L/'paper.ms';s=p.read_text().replace('phi(x)','phi ( x )').replace('phi( "{" 0,1 "}" sup d )','phi ( "{" 0,1 "}" sup d )').replace('h(sigma m)','h( sigma ~ m )').replace('.bp\n.sp 0.5i','.bp\n.HD')
p.write_text(s)
p=L/'scripts/layout.tmac';s=p.read_text().replace('.wh 0 HD','.HD');p.write_text(s)
