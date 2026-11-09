import pathlib,sys,re
D=pathlib.Path(__file__).resolve().parents[1]
t=(D/'sources'/(sys.argv[1]+'.txt')).read_text()
if len(sys.argv)<3:print(t)
else:
 for m in list(re.finditer(sys.argv[2],t))[:int(sys.argv[3]) if len(sys.argv)>3 else 10]:print(t[max(0,m.start()-200):m.start()+1800]+'\n')
