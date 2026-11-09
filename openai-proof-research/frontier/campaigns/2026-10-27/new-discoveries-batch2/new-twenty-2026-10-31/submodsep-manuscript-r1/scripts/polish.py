from pathlib import Path
L=Path(__file__).resolve().parents[1]
p=L/'paper.ms';s=p.read_text()
defs=['.EQ']
for name,glyph in [('phi',r'\(*f'),('sigma',r'\(*s'),('cap',r'\(ca'),('cup',r'\(cu'),('in',r'\(mo'),('notin',r'\(nm'),('subset',r'\(sb'),('subseteq',r'\(ib')]:
 defs.append('define '+name+' /"'+glyph+'"/')
defs+=['.EN']
s=s.replace('delim $$\n.EN','delim $$\n.EN\n'+'\n'.join(defs),1)
s=s.replace('{0,1}','"{" 0,1 "}"').replace('x_i','x sub i').replace('S_5','S sub 5')
s=s.replace('.bp\n','.bp\n.sp 0.5i\n')
p.write_text(s)
