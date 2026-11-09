import re,sys,pathlib
KW=r"well.covered|W_?2.graph|shedding|Tankus|Levit|packing.domination|strong.product|perfect.code|quasi.majority|neighbou?r.sum.distinguish|1-2.conjecture|linear.arboricity|acyclic.edge|acyclic.chromatic|incidence.colou?r|Burris|Schelp|vertex.distinguishing|equitable.total|total.colou?r|ker.diadem|diadem|critical.independent|interval.colou?r|cyclic.interval|deficiency|geodecity|Erd.s.Hajnal|narrow|tensegrit|Euclidean.dimension|unit.distance|Ext.graph|Herden|additive.colou?r|lucky.label|2306\.17272|2510\.02749|2511\.01835|2504\.21452|1611\.07011|1506\.00255|1501\.00204|1911\.08397|1504\.04869|1410\.1591|1202\.6129|1505\.04908|2412\.05352|2110\.11143|1703\.09969|1606\.08827|1608\.00904|1512\.02563|1211\.5122"
ID=r"(?<![0-9a-f])(344558|334658|330309|330625|328966|329573|323109|370752|358956|330517|366150|371290|368238|352331|335703|333481|333717|331997|324533|324536)(?![0-9a-f])"
for f in sys.argv[1:]:
    t=pathlib.Path(f).read_text(errors='replace')
    for pat in (KW,ID):
        for m in re.finditer(pat,t,re.I):
            print(pathlib.Path(f).name,'|',m.group(0),'|',t[max(0,m.start()-70):m.end()+70].replace('\n',' '))
