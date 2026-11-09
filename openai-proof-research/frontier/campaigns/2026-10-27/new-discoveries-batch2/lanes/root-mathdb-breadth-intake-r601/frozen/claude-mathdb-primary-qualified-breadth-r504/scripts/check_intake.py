# Read-only independent intake/corpus/reservation check for r504. Writes JSON report to stdout only.
import hashlib,json,os,sys
B=os.path.realpath(sys.argv[1]); LN=os.path.join(B,'lanes'); I=os.path.join(LN,'root-mathdb-banzhaf-retirement-intake-r503')
P=os.path.join(LN,'pi-mathdb-full-corpus-inventory-r301')
def h(p):
    s=hashlib.sha256(); n=0
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): s.update(b); n+=len(b)
    return s.hexdigest(),n
errs=[]; rep={}
EXP_MAN=('8bc1f5df551d6ee18f89f53812021325ca5fdb159ee1287b9015bbdcc823d4ff',46381)
if h(os.path.join(I,'manifest.json'))!=EXP_MAN: errs.append('intake manifest hash')
man=json.load(open(os.path.join(I,'manifest.json'),encoding='utf-8'))
listed={e['path']:(e['sha256'],e['size']) for e in man['files']}
for p,(s,n) in listed.items():
    q=os.path.join(I,p)
    if not os.path.isfile(q): errs.append('missing '+p); continue
    if h(q)!=(s,n): errs.append('mismatch '+p)
actual=set()
for r,ds,fs in os.walk(I):
    for f in fs: actual.add(os.path.relpath(os.path.join(r,f),I))
extra=sorted(actual-set(listed)-set(man['excluded_exact_paths']))
if extra: errs.append('extra files: %r'%extra)
rep['intake_manifest_files']=len(listed); rep['intake_extra']=extra
bind=json.load(open(os.path.join(I,'bindings.json'),encoding='utf-8')); nb=0
for e in bind:
    for k in ('original','copy'):
        if h(e[k])!=(e['sha256'],e['size']): errs.append('binding %s %s'%(k,e[k]))
    rc=os.path.relpath(e['copy'],I)
    if listed.get(rc)!=(e['sha256'],e['size']): errs.append('copy not manifest-bound '+rc)
    nb+=1
rep['original_copy_pairs']=nb
# r301 manifest: original equals intake-bound copy
c301=os.path.join(I,'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')
if h(os.path.join(P,'manifest.json'))!=h(c301) or listed['frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json']!=h(c301): errs.append('r301 manifest binding')
m301=json.load(open(os.path.join(P,'manifest.json'),encoding='utf-8'))
chunks=[e for e in m301['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
for e in chunks+m301['frozen_inputs']:
    if h(os.path.join(P,e['path']))!=(e['sha256'],e['bytes']): errs.append('r301 '+e['path'])
rep['r301_chunks_checked_in_place']=len(chunks); rep['r301_frozen_inputs_checked']=len(m301['frozen_inputs'])
if len(chunks)!=20 or len(m301['frozen_inputs'])!=8: errs.append('r301 counts')
# reservations
q=json.load(open(os.path.join(I,'queue-r504.json'),encoding='utf-8')); rs=json.load(open(os.path.join(I,'reserved-ids-r504.json'),encoding='utf-8'))
qids=[r['mathdb_id'] for r in q]; ids=rs['ids']
if qids!=ids or len(set(ids))!=50: errs.append('queue/reservation mismatch')
act=json.load(open(os.path.join(I,'active-breadth-reservations.json'),encoding='utf-8'))
mine=[a for a in act if a['lane']=='claude-mathdb-primary-qualified-breadth-r504']
if len(act)!=3 or len(mine)!=1 or mine[0]!=rs: errs.append('active reservation entry')
sets=[set(a['ids']) for a in act]
for i in range(3):
    for j in range(i+1,3):
        if sets[i]&sets[j]: errs.append('active sets overlap')
others=set().union(*[set(a['ids']) for a in act if a['lane']!=rs['lane']])
if others!=set(rs['other_active_reservations']): errs.append('other_active mismatch')
cov=json.load(open(os.path.join(I,'coverage-delta.json'),encoding='utf-8'))
covids={int(k) for k in cov}
rep['coverage_ids']=len(covids)
if len(covids)!=3733: errs.append('coverage count')
S=set(ids)
prot=set(rs['protected_ids'])|{337963,338290,339564,372627}
adj=json.load(open(os.path.join(I,'adjudications.json'),encoding='utf-8')); prot|={int(k) for k in adj}
for name,X in [('coverage',covids),('others',others),('protected',prot)]:
    if S&X: errs.append('overlap with %s: %r'%(name,sorted(S&X)))
# r304 / r363 originals vs intake-bound copies; IDs disjoint
pairs=[('root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','frozen/sol-mathdb-primary-qualified-breadth-r500/frozen/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'),
 ('root-mathdb-accepted-exclusions-r304/historical-dispositions.json','frozen/sol-mathdb-primary-qualified-breadth-r500/frozen/root-mathdb-accepted-exclusions-r304/historical-dispositions.json'),
 ('root-mathdb-cayley-review-intake-r363/DECISION.md','frozen/sol-mathdb-primary-qualified-breadth-r500/frozen/root-mathdb-cayley-review-intake-r363/DECISION.md'),
 ('root-mathdb-cayley-review-intake-r363/disposition.json','frozen/sol-mathdb-primary-qualified-breadth-r500/frozen/root-mathdb-cayley-review-intake-r363/disposition.json'),
 ('root-mathdb-cayley-review-intake-r363/reserved-ids.json','frozen/sol-mathdb-primary-qualified-breadth-r500/frozen/root-mathdb-cayley-review-intake-r363/reserved-ids.json')]
import re
hist=set()
for o,c in pairs:
    if h(os.path.join(LN,o))!=listed.get(c): errs.append('r304/r363 '+o)
    txt=open(os.path.join(LN,o),encoding='utf-8').read()
    hist|={int(x) for x in re.findall(r'(?<!\d)(3\d{5}|4\d{5})(?!\d)',txt)}
rep['r304_r363_numeric_id_tokens']=len(hist)
if S&hist: errs.append('overlap with r304/r363 id tokens: %r'%sorted(S&hist))
rep['reserved']=len(ids); rep['errors']=errs; rep['result']='PASS' if not errs else 'FAIL'
print(json.dumps(rep,indent=1,sort_keys=True)); sys.exit(1 if errs else 0)
