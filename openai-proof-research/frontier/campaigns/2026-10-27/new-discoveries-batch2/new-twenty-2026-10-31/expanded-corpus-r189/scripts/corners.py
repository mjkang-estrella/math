import json,sys,collections
for f in sys.argv[1:]:
    d=json.load(open(f)); by=collections.defaultdict(dict)
    for key,v in d.items():
        s,n=key.split('|'); by[s][int(n)]=v
    corners=lambda s:sum(s[i]!=s[i+1] for i in range(len(s)-1))
    groups=collections.defaultdict(list)
    for s in by: groups[corners(s)].append(s)
    for c,ss in sorted(groups.items()):
        ns=sorted(set.intersection(*[set(by[s]) for s in ss]))
        bad=[n for n in ns if n%4!=2 and len({by[s][n] for s in ss})>1]
        print(f,'corners',c,ss,'n-range',ns[0],ns[-1],'non-2mod4 disagreements at n:',bad)
        for n in bad[:3]: print('   n',n,{s:by[s][n] for s in ss})
