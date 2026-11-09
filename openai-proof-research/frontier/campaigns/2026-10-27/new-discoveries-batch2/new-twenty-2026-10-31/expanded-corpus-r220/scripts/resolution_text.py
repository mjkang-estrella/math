import sys,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from textify import Parser,L
p=L/'receipts/pentanomial-resolution.body';s=Parser();s.feed(p.read_text());(L/'outputs/pentanomial-resolution.txt').write_text(''.join(s.a))
