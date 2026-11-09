from pathlib import Path
p=Path(__file__).with_name('paper.py');s=p.read_text()
s=s.replace(r'.nr PS 11',r'''.char \[dom] \h'1p'\D'l 0 -6p'\D'l 6p 3p'\D'l -6p 3p'\v'2p'\D'l 6p 0'\v'-2p'\h'2p'
.char \[domleft] \h'7p'\v'-6p'\D'l 0 6p'\D'l -6p -3p'\D'l 6p -3p'\v'8p'\D'l -6p 0'\v'-2p'\h'8p'
.nr PS 11''')
s=s.replace(r'\(tE',r'\[dom]').replace(r'\(tL',r'\[domleft]').replace('hookrightarrow','"'+r'\(->'+'"')
p.write_text(s)
