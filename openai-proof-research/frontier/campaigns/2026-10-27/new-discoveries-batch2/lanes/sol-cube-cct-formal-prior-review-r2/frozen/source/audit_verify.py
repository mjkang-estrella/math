from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((L/'pins.json').read_text())
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
assert sha(lean)==pins['lean_sha256']
mf=Path(pins['manifest_original']);assert sha(mf)==pins['manifest_sha256']
heads={}
for pin in pins['packages']:
 p=mf.parent/'.lake/packages'/pin['name']
 gd=p/'.git'
 if gd.is_file():gd=(p/gd.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(gd/'HEAD').read_text().strip()
 if head.startswith('ref: '):
  ref=head[5:]
  if (gd/ref).exists():head=(gd/ref).read_text().strip()
  else:head=next(x.split()[0] for x in (gd/'packed-refs').read_text().splitlines() if x.endswith(' '+ref))
 assert head==pin['rev'],(pin['name'],head,pin['rev'])
 heads[pin['name']]=head
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
builds=[]
for mod in ['Finite','Cube','Endpoint','Audit']:
 r=json.loads((L/(mod+'.guard.json')).read_text());assert r['exit_code']==0 and r['reason'] is None
 builds.append(r)
 if mod!='Audit':assert (L/(mod+'.log')).read_text()==''
for p in L.glob('*.lean'):
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',p.read_text())
manifest=json.loads((L/'source-manifest.json').read_text())
assert all(sha(L/n)==h for n,h in manifest.items())
r={'component_status':'PASS','source_endpoint_status':'PROVED_N5','endpoint':'Cube.literal_question66_false',
 'actual_declaration_count':len(decls),'declarations':[{'name':n,'origin':o,'unsafe':False,'safety':safety[n],'axioms':ax[n]} for n,o,_ in decls],
 'imported_declarations':'inherited pinned library, not counted as new declarations; endpoint dependency closures audited',
 'generated_partial_declarations':[n for n,v in safety.items() if v.endswith('.partial')],
 'all_actual_types':'Audit.log, pp.all=true, no ellipsis','package_heads':heads,'builds':builds,
 'source_hashes_unchanged':True,'claims':'Unconditional n=5 literal Question6.6 negation for all real linear cube automorphisms; all-n extension not formalized; novelty HOLD'}
(L/'replay-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['component_status','source_endpoint_status','actual_declaration_count','generated_partial_declarations']}))
