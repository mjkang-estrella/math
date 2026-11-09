import re,sys
P=re.compile(r"Kikuta|Kote|warmth|strong resolving|Alspach|partial-sum sequenc|bipartite Kneser|Latin square graph|feedback vertex|normal rational curve|dimatroid|Exoo|Lee.Zhang|1501\.00573|1612\.02843|1510\.02521|1511\.05384|1511\.07866|1504\.03662|1612\.07652|1509\.01185|1510\.02075|1504\.01949|1807\.04741|1505\.06984|1506\.02517|1612\.05447",re.I)
for f in open(sys.argv[1]).read().split():
    if 'r165' in f: continue
    try: t=open(f,encoding='utf-8',errors='replace').read()
    except Exception: continue
    ms=list(P.finditer(t))
    if not ms: continue
    print('##',f,len(ms))
    for m in ms[:3]: print('   ',t[max(0,m.start()-150):m.end()+150].replace('\n',' '))
