import pathlib,re,sys
D=pathlib.Path(__file__).resolve().parents[1]
for a in sys.argv[1:]:
 p=D/'outputs'/(a+'-html.txt');t=p.read_text();print('\nSOURCE',a)
 for m in list(re.finditer(r'(?i)conjectur|mirror|verified|computed',t))[:22]: print(t[max(0,m.start()-180):m.start()+1000])
