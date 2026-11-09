from pathlib import Path
L=Path(__file__).resolve().parents[1]
p=L/'paper.ms';s=p.read_text()
s=s.replace(r'\{','"{"').replace(r'\}','"}"').replace(r'\mathrm{Fin}','roman Fin')
s=s.replace('binom d k','left ( {d} above {k} right )').replace('binom d {<= r}','left ( {d} above {<= r} right )').replace('binom t 2','left ( {t} above {2} right )')
# Restore normal text font after each section heading.
lines=s.splitlines();out=[]
for i,line in enumerate(lines):
 out.append(line)
 if i>0 and lines[i-1].startswith('.NH'):
  out.extend(['.ft R','.ps 11'])
p.write_text('\n'.join(out)+'\n')
p=L/'scripts/build_pdf.py';s=p.read_text().replace("'-ms',","str(L/'scripts/layout.tmac'),");p.write_text(s)
