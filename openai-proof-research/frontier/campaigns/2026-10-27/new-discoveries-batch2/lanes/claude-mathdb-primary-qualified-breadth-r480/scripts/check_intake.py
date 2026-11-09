import json,hashlib,os,sys
L=sys.argv[1]; I=os.path.join(L,'root-mathdb-breadth-intake-r479')
def h(p):
    b=open(p,'rb').read(); return hashlib.sha256(b).hexdigest(),len(b)
out={'manifest':{},'bindings':{}}
m=json.load(open(os.path.join(I,'manifest.json')))
listed={f['path'] for f in m['files']}
actual=set()
for r,ds,fs in os.walk(I):
    for f in fs: actual.add(os.path.relpath(os.path.join(r,f),I))
bad=[f['path'] for f in m['files'] if not os.path.exists(os.path.join(I,f['path'])) or h(os.path.join(I,f['path']))!=(f['sha256'],f['size'])]
out['manifest']={'listed':len(listed),'actual':len(actual),'unlisted_actual':sorted(actual-listed),'missing_or_mismatch':bad}
b=json.load(open(os.path.join(I,'bindings.json')))
base=L  # resolve paths
bb=[];roots=set()
for e in b:
    res={}
    for k in ('original','copy'):
        p=e[k]
        cands=[p, os.path.join(L,p), os.path.join(I,p), os.path.join(os.path.dirname(L),p)]
        q=next((c for c in cands if os.path.isfile(c)),None)
        res[k]=q is not None and h(q)==(e['sha256'],e['size'])
        if q is None: res[k+'_path']='NOTFOUND:'+p
    if not all(res[k] for k in ('original','copy')): bb.append((e,res))
    roots.add(e['original'].split('/')[0])
out['bindings']={'count':len(b),'failures':bb[:10],'nfail':len(bb),'original_roots':sorted(roots)[:40],'sample':b[:3]}
print(json.dumps(out,indent=1))
