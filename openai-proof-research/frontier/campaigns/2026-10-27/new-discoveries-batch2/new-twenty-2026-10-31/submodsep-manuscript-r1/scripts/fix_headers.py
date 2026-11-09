from pathlib import Path
L=Path(__file__).resolve().parents[1]
p=L/'scripts/layout.tmac';s=p.read_text().replace('.wh -0.45i FT','').replace('.sp 0.3i','.sp |0.3i')
s+='\n.de MXfooter\n.sp |10.5i\n.ps 9\n.tl \'\'\\\\n%\'\'\n.ps 11\n..\n'
p.write_text(s)
p=L/'paper.ms';s=p.read_text().replace('.bp\n','.MXfooter\n.bp\n');s+='\n.MXfooter\n';p.write_text(s)
