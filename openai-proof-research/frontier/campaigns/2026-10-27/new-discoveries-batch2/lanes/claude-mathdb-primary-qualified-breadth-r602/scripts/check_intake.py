# Read-only independent intake/corpus/reservation check for Claude r602.
# Assignment authority: root r601 (immutable). Current coverage/adjudication/reservation authority: root r603.
# Does not execute any upstream verify.py. Writes a JSON report to stdout only; nonzero exit on any mismatch.
import hashlib,json,os,re,sys
B=os.path.realpath(sys.argv[1]); LN=os.path.join(B,'lanes')
I1=os.path.join(LN,'root-mathdb-breadth-intake-r601'); I3=os.path.join(LN,'root-mathdb-breadth-intake-r603')
P=os.path.join(LN,'pi-mathdb-full-corpus-inventory-r301'); ME='claude-mathdb-primary-qualified-breadth-r602'
def h(p):
    s=hashlib.sha256(); n=0
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): s.update(b); n+=len(b)
    return s.hexdigest(),n
def J(p): return json.load(open(p,encoding='utf-8'))
errs=[]; rep={}
PIN={I1:('fd199b647c5c807000277477af312eafe6182a53b8519c52653549cf9639f02f',16780),
     I3:('a8261dc455e6b6438fe4714cab0af16a8b33581f671d6723d8e6c3740e137a90',9761)}
RCPT={I1:('daee70f012f8019aa2cd4700a2002f26319455211758d6b72497271bd3759688',512),
      I3:('1d122031e3d4e8b4477d811bbc7bf8bbd0082ebe1b3faa582e1cb2bce35ada71',509)}
listed={}
for I in (I1,I3):
    tag=os.path.basename(I)
    if h(os.path.join(I,'manifest.json'))!=PIN[I]: errs.append(tag+' manifest pin')
    if h(os.path.join(I,'verification-receipt.json'))!=RCPT[I]: errs.append(tag+' receipt pin')
    man=J(os.path.join(I,'manifest.json')); L={e['path']:(e['sha256'],e['size']) for e in man['files']}; listed[I]=L
    for p,v in L.items():
        q=os.path.join(I,p)
        if not os.path.isfile(q): errs.append(tag+' missing '+p)
        elif h(q)!=v: errs.append(tag+' mismatch '+p)
    actual=set()
    for r,ds,fs in os.walk(I):
        for f in fs: actual.add(os.path.relpath(os.path.join(r,f),I))
    extra=sorted(actual-set(L)-set(man['excluded_exact_paths']))
    if extra: errs.append(tag+' extra files %r'%extra)
    nb=0
    for e in J(os.path.join(I,'bindings.json')):
        for k in ('original','copy'):
            if h(e[k])!=(e['sha256'],e['size']): errs.append('%s binding %s %s'%(tag,k,e[k]))
        rc=os.path.relpath(e['copy'],I)
        if L.get(rc)!=(e['sha256'],e['size']): errs.append(tag+' copy not manifest-bound '+rc)
        nb+=1
    rep[tag]={'manifest_files':len(L),'extra':extra,'original_copy_pairs':nb}
# r603 freezes r601 exactly
for f in ['manifest.json','verification-receipt.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','active-breadth-reservations.json','reserved-ids.json','routing-queue.jsonl','verify.py']:
    if listed[I3].get('frozen/root-mathdb-breadth-intake-r601/'+f)!=h(os.path.join(I1,f)): errs.append('r603 frozen r601 copy '+f)
# r301 inventory manifest: original == both intake-bound copies
c='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'
o=h(os.path.join(P,'manifest.json'))
if o!=listed[I1].get(c) or o!=listed[I3].get(c): errs.append('r301 manifest binding')
m301=J(os.path.join(P,'manifest.json'))
chunks=[e for e in m301['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
for e in chunks+m301['frozen_inputs']:
    if h(os.path.join(P,e['path']))!=(e['sha256'],e['bytes']): errs.append('r301 '+e['path'])
rep['r301_chunks_checked_in_place']=len(chunks); rep['r301_frozen_inputs_checked']=len(m301['frozen_inputs'])
if len(chunks)!=20 or len(m301['frozen_inputs'])!=8: errs.append('r301 counts')
# assignment (r601) and current reservations (r603)
q=J(os.path.join(I1,'queue.json')); rs=J(os.path.join(I1,'reserved-ids.json'))
ids=rs['ids']; S=set(ids)
if rs['lane']!=ME or [r['mathdb_id'] for r in q]!=ids or len(S)!=50: errs.append('queue/reservation mismatch')
act=J(os.path.join(I3,'active-breadth-reservations.json'))
lanes=sorted(a['lane'] for a in act)
if lanes!=sorted([ME,'sol-mathdb-primary-qualified-breadth-r600','sol-mathdb-primary-qualified-breadth-r604']): errs.append('current active lanes %r'%lanes)
mine=[a for a in act if a['lane']==ME]
IMM=('ids','lane','coverage_baseline','protected_ids','status','active_hypothesis_ids')
if len(mine)!=1 or any(mine[0].get(k)!=rs.get(k) for k in IMM): errs.append('r603 active entry != r601 assignment')
rep['r601_vs_r603_entry_differs_only_in']=sorted(k for k in set(rs)|set(mine[0] if mine else {}) if (mine and mine[0].get(k)!=rs.get(k)))
sets={a['lane']:set(a['ids']) for a in act}
ln=list(sets)
for i in range(len(ln)):
    for j in range(i+1,len(ln)):
        if sets[ln[i]]&sets[ln[j]]: errs.append('active overlap %s %s'%(ln[i],ln[j]))
others=set().union(*[v for k,v in sets.items() if k!=ME])
if mine and set(mine[0]['other_active_reservations'])!=others: errs.append('r603 other_active mismatch')
cov=J(os.path.join(I3,'coverage-delta.json')); covids={int(k) for k in cov}
rep['current_coverage_ids']=len(covids)
if len(covids)!=6033: errs.append('coverage count')
# completed r504 and r598 assignments must be in coverage, not reserved
r504=J(os.path.join(LN,'root-mathdb-banzhaf-retirement-intake-r503/reserved-ids-r504.json'))['ids']
r598=[a for a in J(os.path.join(I1,'active-breadth-reservations.json')) if a['lane']=='sol-mathdb-primary-qualified-breadth-r598'][0]['ids']
if not set(r504)<=covids or not set(r598)<=covids: errs.append('completed r504/r598 not in coverage')
if (set(r504)|set(r598))&(others|S): errs.append('completed ids re-reserved')
prot=set(rs['protected_ids'])|{337963,338290,339564,372627}
prot|={int(k) for k in J(os.path.join(I3,'adjudications.json'))}
prot|={x['mathdb_id'] for x in J(os.path.join(I3,'hypothesis-queue.json'))}
for name,X in [('coverage',covids),('other_active',others),('protected',prot)]:
    if S&X: errs.append('overlap with %s: %r'%(name,sorted(S&X)))
# r304 / r363 originals pinned (also equal r301 frozen inputs for r304)
PINS={'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json':('f1883cb41f2bb21f1d5d3125372fa900d535e70a6601cb411423d6b896d9fe64',55646),
 'root-mathdb-accepted-exclusions-r304/historical-dispositions.json':('07f2dae9e96bd40bbce4fb16263609210e54ff151568f8abd53b448ce774cebc',82182),
 'root-mathdb-cayley-review-intake-r363/DECISION.md':('1c1d8d1048e722826cdfbd8e93d8320dc07cdf5ff62980dc33b8e6db34c07256',1922),
 'root-mathdb-cayley-review-intake-r363/disposition.json':('27b170a4a4a5be40441944edf20bda7a3f9c8c9b68fd13819c917f2b822d35dd',583),
 'root-mathdb-cayley-review-intake-r363/reserved-ids.json':('df789395f8c399293558595c2bc8b0302d9b4f5c0f4f3668fddcfb53a642dabb',785)}
hist=set()
for p,v in PINS.items():
    if h(os.path.join(LN,p))!=v: errs.append('pin '+p)
    hist|={int(x) for x in re.findall(r'(?<!\d)([1-4]\d{5})(?!\d)',open(os.path.join(LN,p),encoding='utf-8').read())}
rep['r304_r363_numeric_id_tokens']=len(hist)
if S&hist: errs.append('overlap with r304/r363 id tokens: %r'%sorted(S&hist))
rep['reserved']=len(ids); rep['other_active']=len(others); rep['protected']=len(prot)
rep['errors']=errs; rep['result']='PASS' if not errs else 'FAIL'
print(json.dumps(rep,indent=1,sort_keys=True)); sys.exit(1 if errs else 0)
