import pathlib,re,sys
D=pathlib.Path(__file__).resolve().parents[1]
p=D/'sources'/(sys.argv[1]+'.txt');s=p.read_text();print('SOURCE',p)
for m in list(re.finditer(sys.argv[2],s,re.I))[:int(sys.argv[3]) if len(sys.argv)>3 else 8]: print('\n',s[max(0,m.start()-250):m.start()+1800])
