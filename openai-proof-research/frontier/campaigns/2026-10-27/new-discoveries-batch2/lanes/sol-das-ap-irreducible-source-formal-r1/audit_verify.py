from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
log=(L/'Audit.log').read_text()
assert '⋯' not in log
decls=re.findall(r'^DECL\|(.+?)\|ORIGIN\|(.+?)\|UNSAFE\|(false|true)$',log,re.M)
assert decls and all(u=='false' for _,_,u in decls)
safety=dict(re.findall(r'^SAFETY\|(.+?)\|(.+)$',log,re.M))
assert set(safety)=={n for n,_,_ in decls}
reports=dict(re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.M))
for n in re.findall(r"^'([^']+)' does not depend on any axioms",log,re.M):reports[n]=''
assert set(reports)==set(safety)
ax={n:[a.strip() for a in re.sub(r'\.\{[^}]+\}','',s).split(',')] if s else [] for n,s in reports.items()}
allow={'propext','Classical.choice','Quot.sound'}
assert all(set(a)<=allow for a in ax.values())
assert not any(v.endswith('.partial') for v in safety.values())
assert 'Das.literal_universal_bound_false' in safety
builds=[]
for mod in ['Definitions','Witness','Audit']:
 r=json.loads((L/(mod+'.guard.json')).read_text());assert r['exit_code']==0 and r['reason'] is None
 builds.append(r)
 if mod!='Audit':assert (L/(mod+'.log')).read_text()==''
for p in L.glob('*.lean'):
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',p.read_text())
manifest=json.loads((L/'source-manifest.json').read_text())
assert all(sha(L/n)==h for n,h in manifest.items())
r={'component_status':'PASS','source_endpoint_status':'PROVED_LITERAL_N5_REFUTATION','endpoint':'Das.literal_universal_bound_false',
 'actual_declaration_count':len(decls),'declarations':[{'name':n,'origin':o,'unsafe':False,'safety':safety[n],'axioms':ax[n]} for n,o,_ in decls],
 'imported_declarations':'inherited pinned library, not counted as new declarations; endpoint dependency closures audited',
 'generated_partial_declarations':[n for n,v in safety.items() if v.endswith('.partial')],
 'all_actual_types':'Audit.log, pp.all=true, no ellipsis','pins_verification':'verify_pins.py before and after replay','builds':builds,
 'source_hashes_unchanged':True,'claims':'Unconditional literal universal Conjecture5.1 negation via n5; published-source and novelty HOLD; no acceptance/count change'}
(L/'replay-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['component_status','source_endpoint_status','actual_declaration_count','generated_partial_declarations']}))
