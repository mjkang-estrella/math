import re,sys,os,json
D=sys.argv[1]
for a in sys.argv[2:]:
    t=open(os.path.join(D,a+'.txt'),encoding='utf-8',errors='replace').read().split('\n')
    v=next((m.group(0) for l in t for m in [re.search(r'arXiv:'+re.escape(a)+r'v\d+',l)] if m),'?')
    hits=[(i+1,l.strip()[:110]) for i,l in enumerate(t) if re.search(r'(Conjecture|Problem|Question)\s*[0-9]+(\.[0-9]+)*\s*[.(:]|conjecture[ds]? that|We conjecture|conjectured',l)]
    print('##',a,v,len(t),'lines')
    for h in hits[:9]: print('  ',h[0],h[1])
