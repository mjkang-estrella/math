#!/usr/bin/env python3
# Independent READ-ONLY verifier for lane claude-mathdb-primary-qualified-breadth-r504.
# Usage: python3 -B -I verify.py [LANE_DIR [CAMPAIGN_BASE]]   Exit 0 = integrity PASS; 1 = any mismatch.
# Integrity PASS is NOT a mathematics, novelty or registry PASS.
import hashlib,json,os,sys
L=os.path.realpath(sys.argv[1]) if len(sys.argv)>1 else os.path.dirname(os.path.realpath(__file__))
B=os.path.realpath(sys.argv[2]) if len(sys.argv)>2 else os.path.realpath(os.path.join(L,'../..'))
LN=os.path.join(B,'lanes'); I=os.path.join(LN,'root-mathdb-banzhaf-retirement-intake-r503'); P=os.path.join(LN,'pi-mathdb-full-corpus-inventory-r301')
EXCL={'manifest.json','final-receipt.json'}
INTAKE_MANIFEST=('8bc1f5df551d6ee18f89f53812021325ca5fdb159ee1287b9015bbdcc823d4ff',46381)
R301_MANIFEST=('4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15',22047)
errs=[]; info={}
def h(p):
    s=hashlib.sha256(); n=0
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): s.update(b); n+=len(b)
    return s.hexdigest(),n
def J(p): 
    with open(p,encoding='utf-8') as f: return json.load(f)
def safe(label,fn):
    try: fn()
    except Exception as e: errs.append('%s: exception %r'%(label,e))
# 1 lane manifest: exact payload, no extra/missing files
def c1():
    m=J(os.path.join(L,'manifest.json')); listed={e['path']:(e['sha256'],e['size']) for e in m['files']}
    if set(m.get('excluded_exact_paths',[]))!=EXCL: errs.append('manifest exclusions altered')
    for p,v in listed.items():
        q=os.path.join(L,p)
        if not os.path.isfile(q): errs.append('missing payload '+p)
        elif h(q)!=v: errs.append('payload hash/size mismatch '+p)
    act=set()
    for r,ds,fs in os.walk(L):
        for f in fs: act.add(os.path.relpath(os.path.join(r,f),L))
    extra=sorted(act-set(listed)-EXCL)
    if extra: errs.append('extra files %r'%extra)
    info['payload_files']=len(listed)
safe('manifest',c1)
# 2 flat bindings to originals (in place)
def c2():
    fb=J(os.path.join(L,'flat-bindings.json'))
    for e in fb:
        if not os.path.isfile(e['original']) or h(e['original'])!=(e['sha256'],e['size']): errs.append('flat binding mismatch '+e['original'])
    info['flat_bindings']=len(fb)
safe('flat',c2)
# 3 intake manifest + exact intake payload; r301 manifest, 20 chunks, 8 frozen inputs in place
def c3():
    if h(os.path.join(I,'manifest.json'))!=INTAKE_MANIFEST: errs.append('intake manifest hash')
    im=J(os.path.join(I,'manifest.json')); il={e['path']:(e['sha256'],e['size']) for e in im['files']}
    for p,v in il.items():
        if h(os.path.join(I,p))!=v: errs.append('intake payload '+p)
    act=set()
    for r,ds,fs in os.walk(I):
        for f in fs: act.add(os.path.relpath(os.path.join(r,f),I))
    if act-set(il)-set(im['excluded_exact_paths']): errs.append('intake extra files')
    for e in J(os.path.join(I,'bindings.json')):
        if h(e['original'])!=(e['sha256'],e['size']) or h(e['copy'])!=(e['sha256'],e['size']): errs.append('intake original/copy '+e['original'])
    if h(os.path.join(P,'manifest.json'))!=R301_MANIFEST or il.get('frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')!=R301_MANIFEST: errs.append('r301 manifest vs intake binding')
    m=J(os.path.join(P,'manifest.json'))
    ch=[e for e in m['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
    if len(ch)!=20 or len(m['frozen_inputs'])!=8: errs.append('r301 counts')
    for e in ch+m['frozen_inputs']:
        if h(os.path.join(P,e['path']))!=(e['sha256'],e['bytes']): errs.append('r301 in place '+e['path'])
    info['r301_chunks']=len(ch); info['r301_frozen_inputs']=len(m['frozen_inputs'])
safe('intake/r301',c3)
# 4 reservation and disjointness
def c4():
    rs=J(os.path.join(I,'reserved-ids-r504.json')); ids=rs['ids']
    q=[r['mathdb_id'] for r in J(os.path.join(I,'queue-r504.json'))]
    d=J(os.path.join(L,'dispositions.json')); did=[x['mathdb_id'] for x in d]
    if not (ids==q==did and len(set(ids))==50): errs.append('reservation/queue/dispositions mismatch')
    act=J(os.path.join(I,'active-breadth-reservations.json')); S=set(ids)
    sets=[set(a['ids']) for a in act]
    if len(act)!=3 or any(sets[i]&sets[j] for i in range(3) for j in range(i+1,3)): errs.append('active sets not disjoint')
    others=set().union(*[set(a['ids']) for a in act if a['lane']!=rs['lane']])
    cov={int(k) for k in J(os.path.join(I,'coverage-delta.json'))}
    prot=set(rs['protected_ids'])|{int(k) for k in J(os.path.join(I,'adjudications.json'))}|{337963,338290,339564,372627}
    if len(cov)!=3733: errs.append('coverage baseline count')
    for n,X in (('coverage',cov),('other reservations',others),('protected',prot)):
        if S&X: errs.append('overlap %s %r'%(n,sorted(S&X)))
    if len(J(os.path.join(L,'proposals.json')))>3: errs.append('more than three proposals')
safe('reservation',c4)
# 5 literal statements and canonical record hashes re-derived from chunks in place
def c5():
    d=J(os.path.join(L,'dispositions.json')); lines={}
    for x in d: lines.setdefault(x['corpus_chunk'],{})[x['corpus_line']]=x
    n=0
    for c,want in lines.items():
        with open(os.path.join(P,c),'rb') as f:
            for ln,raw in enumerate(f,1):
                if ln in want:
                    x=want[ln]; r=json.loads(raw.decode('utf-8'))
                    can=json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')
                    ok=(r['mathdb_id']==x['mathdb_id'] and hashlib.sha256(can).hexdigest()==x['canonical_record_sha256']
                        and hashlib.sha256(raw.rstrip(b'\n')).hexdigest()==x['corpus_line_sha256'] and r['statement']==x['statement']
                        and hashlib.sha256(r['statement'].encode('utf-8')).hexdigest()==x['statement_utf8_sha256'] and x['credit']==0)
                    if not ok: errs.append('record mismatch %s'%x['mathdb_id'])
                    n+=1
    if n!=50: errs.append('records located %d'%n)
    info['records_rederived']=n
safe('records',c5)
res={'lane':'claude-mathdb-primary-qualified-breadth-r504','result':'PASS' if not errs else 'FAIL','errors':errs,'info':info,
     'scope':'integrity only; not a mathematics, novelty or registry PASS'}
print(json.dumps(res,indent=1,sort_keys=True)); sys.exit(0 if not errs else 1)
