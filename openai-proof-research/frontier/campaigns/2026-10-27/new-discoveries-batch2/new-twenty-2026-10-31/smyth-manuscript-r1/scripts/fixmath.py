from pathlib import Path
p=Path(__file__).with_name('paper.py');s=p.read_text();a=s.index('def mathfix');b=s.index("s=s.replace('U^m_n'",a)
s=s[:a]+r'''s=s.replace('lambda',r'\(*l')
s=s.replace(' member ',r' "\(mo" ')
'''+s[b:];p.write_text(s)
