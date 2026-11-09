from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((L/'pins.json').read_text())
assert sha(Path(p['lean']))==p['lean_sha256']
heads={}
for r in p['packages']:
    g=Path(p['formal'])/'.lake/packages'/r['name']/'.git'
    h=(g/'HEAD').read_text().strip()
    if h.startswith('ref: '):h=(g/h[5:]).read_text().strip()
    assert h==r['revision']
    heads[r['name']]=h
log=(L/'Audit.log').read_text()
assert '⋯' not in log
decls=re.findall(r'^DECL\|(.+?)\|ORIGIN\|(.+?)\|UNSAFE\|(false|true)$',log,re.M)
assert decls and all(u=='false' for _,_,u in decls)
safety=dict(re.findall(r'^SAFETY\|(.+?)\|(.+)$',log,re.M))
reports=dict(re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.M))
for n in re.findall(r"^'([^']+)' does not depend on any axioms",log,re.M):reports[n]=''
assert set(reports)==set(safety)=={n for n,_,_ in decls}
axioms={n:[a.strip() for a in re.sub(r'\.\{[^}]+\}','',s).split(',')] if s else [] for n,s in reports.items()}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
assert not any(v.endswith('.partial') for v in safety.values())
for mod in ['Reduction','Symmetry','Source','Expansion','Audit']:
    r=json.loads((L/(mod+'.guard.json')).read_text())
    assert r['exit_code']==0 and r['reason'] is None
    if mod!='Audit':assert not (L/(mod+'.log')).read_text()
for mod in ['Reduction','Symmetry','Source','Expansion','Audit']:
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|partial)\b',(L/(mod+'.lean')).read_text())
r={'component_status':'PASS','literal_endpoint_status':'NOT_PROVED',
   'remaining_interface':'FloorSums.SortedClampedBound is defined, not proved',
   'actual_declaration_count':len(decls),'package_heads':heads,
   'declarations':[{'name':n,'origin':o,'unsafe':False,'safety':safety[n],'axioms':axioms[n]} for n,o,_ in decls],
   'types':'Audit.log, pp.all=true; transitive axioms for every owned declaration, including generated/private',
   'generated_partial_declarations':[]}
(L/'audit-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['component_status','literal_endpoint_status','actual_declaration_count']}))
