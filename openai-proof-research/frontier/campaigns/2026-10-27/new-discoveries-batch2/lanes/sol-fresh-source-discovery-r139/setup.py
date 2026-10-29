from pathlib import Path
L=Path(__file__).resolve().parent
s=(L.parent/'sol-fresh-source-discovery-r135/history.py').read_text()
a=s.index('P=re.compile(');b=s.index('\ndef sha',a)
s=s[:a]+"P=re.compile(rb'2610[.]22142|wild.{0,12}number|Dawkins|Nappo|Zimbizi|Tong.{0,40}spanning',re.I)"+s[b:]
(L/'history.py').write_text(s)
s=(L.parent/'sol-fresh-source-discovery-r137/work.py').read_text()
(L/'work.py').write_text(s)
