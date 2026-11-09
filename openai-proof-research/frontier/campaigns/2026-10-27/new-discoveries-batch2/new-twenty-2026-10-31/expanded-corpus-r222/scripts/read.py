import pathlib,re,sys
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'sources'/(sys.argv[1]+'.txt')).read_text()
for m in list(re.finditer(sys.argv[2],s,re.I))[:int(sys.argv[3]) if len(sys.argv)>3 else 8]:print(s[max(0,m.start()-250):m.end()+1600]+'\n\n')
