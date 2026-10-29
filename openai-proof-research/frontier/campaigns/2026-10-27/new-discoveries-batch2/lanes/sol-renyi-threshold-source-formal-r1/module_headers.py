from pathlib import Path
for name in ['Pointwise','Majorant','Tail']:
 p=Path('formal')/(name+'.lean');s=p.read_text()
 s='module\n'+s.replace('import ','public import ')
 i=s.index('set_option')
 s=s[:i]+'public section\n'+s[i:]
 p.write_text(s)
