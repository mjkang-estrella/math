import json,re,sys
out={}
for sec in ['D5','Problems']:
    old={t['path']:t['sha'] for t in json.load(open(f'../staller-source-significance-review-r1/omega-{sec}.json'))['tree']}
    newd=json.load(open(f'downloads/registry/omega-{sec}.json'))
    new={t['path']:t['sha'] for t in newd['tree']}
    out[sec]={'truncated':newd['truncated'],'n_old':len(old),'n_new':len(new),
      'added':sorted(set(new)-set(old)),'removed':sorted(set(old)-set(new)),
      'modified':sorted(p for p in new if p in old and new[p]!=old[p])}
pat=re.compile(sys.argv[1],re.I)
hits={sec:[t['path'] for t in json.load(open(f'downloads/registry/omega-{sec}.json'))['tree'] if pat.search(t['path'])] for sec in ['D5','Problems']}
json.dump({'pattern':sys.argv[1],'changes':out,'hits':hits},open('checks/omega-diff-and-hits.json','w'),indent=1)
for sec in out: print(sec,{k:(v if not isinstance(v,list) else len(v)) for k,v in out[sec].items()})
for sec in out:
    for k in ['added','removed','modified']: print(sec,k,[p for p in out[sec][k] if p.endswith('.lean') or '/' not in p][:40])
print(json.dumps(hits,indent=0)[:3000])
