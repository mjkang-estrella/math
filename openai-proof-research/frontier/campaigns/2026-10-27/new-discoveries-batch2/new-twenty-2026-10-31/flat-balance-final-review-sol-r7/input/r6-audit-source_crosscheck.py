import json,re,hashlib
lane='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/flat-balance-independent-audit-pi-r6'
env=json.load(open(lane+'/results/352972-env-audit.json'))
srcA=open(lane+'/src/FlatBalance.lean').read()
srcB=open(lane+'/src/FlatBalanceBridges.lean').read()
decls=env['declarations']

def classify(n,module):
    src = srcB if module=='FlatBalanceBridges' else srcA
    s=n
    m=re.match(r'_private\.src\.(FlatBalance|FlatBalanceBridges)\.\d+\.(.*)$',s)
    if m:
        s=m.group(2)
    for ns in ('FlatBalance.','FlatBalanceBridges.'):
        if s.startswith(ns): s=s[len(ns):]
    parts=s.split('.')
    cands=['.'.join(parts[:k]) for k in range(len(parts),0,-1)]
    leg=parts[-1]
    leg2=re.sub(r'(_proof_\d+|_simp_\d+_\d+|_sparseCasesOn_\d+|_\d+)$','',leg)
    eqmatch=re.match(r'eq_(\d+)$',leg)
    auxgen={'recOn','rec','noConfusion','noConfusionType','casesOn','ctorIdx','inj','injEq',
            'sizeOf_spec','_flat_ctor','mk','splitter'}
    for c in cands:
        if re.search(r'(?<![A-Za-z0-9_.])'+re.escape(c)+r'(?![A-Za-z0-9_.])',src):
            return ('explicit',c)
    if re.search(r'(?<![A-Za-z0-9_.])'+re.escape(leg2)+r'(?![A-Za-z0-9_.])',src):
        return ('generated_suffix_of_source_name',leg2)
    owner='.'.join(parts[:-1])
    o=re.sub(r'^_private\.src\.(FlatBalance|FlatBalanceBridges)\.\d+\.','',owner)
    for ns in ('FlatBalance.','FlatBalanceBridges.'):
        if o.startswith(ns): o=o[len(ns):]
    owner_present=bool(re.search(r'(?<![A-Za-z0-9_.])'+re.escape(o)+r'(?![A-Za-z0-9_.])',src))
    if owner.endswith('SimpleGraph') or leg in ('Adj','adj_symm','adj_irrefl'):
        fld=leg if leg in ('Adj','adj_symm','adj_irrefl') else None
        if fld and re.search(r'(?<![A-Za-z0-9_.])'+fld+r'(?![A-Za-z0-9_.])',src):
            return ('structure_field_or_projection',fld)
        if owner_present or owner.endswith('SimpleGraph'):
            return ('auto_generated_structure_aux',leg)
    if (eqmatch or leg in auxgen or leg.startswith('_simp') or leg.startswith('_proof')
        or leg.startswith('_sparseCasesOn') or leg.startswith('match_')) and owner_present:
        return ('generated_aux_of_source_owner',o)
    return ('unexplained',None)

counts={}; unexplained=[]; detail=[]
for d in decls:
    n=d['name']; mod=d['module']
    if mod not in ('FlatBalance','FlatBalanceBridges'):
        unexplained.append((n,'origin-not-production')); continue
    cat,how=classify(n,mod)
    counts[cat]=counts.get(cat,0)+1
    detail.append({'name':n,'class':cat,'via':how})
    if cat=='unexplained': unexplained.append((n,'no rule'))
tokenScan={t:sorted(set(re.findall(t,srcA))|set(re.findall(t,srcB))) for t in
     [r'sorry',r'admit',r'axiom',r'unsafe',r'partial',r'opaque',
      r'native_decide',r'extern',r'implemented_by']}
attrScan=re.findall(r'@\[(\w+)',srcA+srcB)
rec={'source_crosscheck':{
  'declCount':len(decls),
  'classificationCounts':counts,
  'unexplained':unexplained,
  'tokenScanInstances':tokenScan,
  'tokenScanNote':'occurrences include doc-comment prose; env-audit kinds/safety are authoritative',
  'attributesInSources':attrScan,
  'detail':detail,
  'sourceHashes':{
    'FlatBalance.lean':hashlib.sha256(srcA.encode()).hexdigest(),
    'FlatBalanceBridges.lean':hashlib.sha256(srcB.encode()).hexdigest()}}}
open(lane+'/results/source-crosscheck.json','w').write(json.dumps(rec,indent=2))
print(json.dumps(rec['source_crosscheck']['classificationCounts'],indent=1))
print('unexplained:',rec['source_crosscheck']['unexplained'])
print('tokens:',tokenScan)
print('attributes:',attrScan)
