import json,hashlib,os,sys
B=sys.argv[1]; I=B+'/lanes/root-mathdb-three-candidate-intake-r493'
F='frozen/claude-mathdb-primary-qualified-breadth-r480/'
def h(p):
    d=open(p,'rb').read(); return hashlib.sha256(d).hexdigest(),len(d)
m=json.load(open(I+'/manifest.json'))
ent={e['path']:e for e in m['files']}
print('intake manifest entries',len(ent),'excluded',m.get('excluded_exact_paths'))
bad=0
# full exact manifest check: every file in intake dir listed, except exclusions
listed=set(ent); actual=set()
for r,ds,fs in os.walk(I):
    for f in fs:
        actual.add(os.path.relpath(os.path.join(r,f),I))
extra=actual-listed-set(m.get('excluded_exact_paths',[])); missing=listed-actual
print('unlisted',sorted(extra)[:20],len(extra)); print('missing',sorted(missing)[:20],len(missing))
for p,e in ent.items():
    if p in actual:
        s,n=h(I+'/'+p)
        if s!=e['sha256'] or n!=e['size']: bad+=1; print('MISMATCH',p)
print('intake hash mismatches',bad)
need=['briefs/P1-338290-banzhaf-counterexample.md','sources/arxiv/1801.08029.pdf','sources/arxiv/1801.08029.txt','scripts/banzhaf.py','runs/banzhaf.r1.txt','retained-sources.json','sources/fetch-log.txt','manifest.json']
for n in need: print('in-intake-manifest',n,(F+n) in ent)
# direct original vs copy
O=B+'/lanes/claude-mathdb-primary-qualified-breadth-r480/'
om=json.load(open(I+'/'+F+'manifest.json'))
oent={e['path']:e for e in om['files']} if 'files' in om else {}
print('r480 manifest keys',list(om.keys())[:6],len(oent))
for n in need:
    c=h(I+'/'+F+n)
    if os.path.exists(O+n):
        o=h(O+n); print('orig==copy',n,o==c,c[0][:16],c[1])
    else: print('ORIG MISSING',n)
    if n in oent: print('  r480-manifest match',(oent[n]['sha256'],oent[n]['size'])==c)
    else: print('  not in r480 manifest',n)
