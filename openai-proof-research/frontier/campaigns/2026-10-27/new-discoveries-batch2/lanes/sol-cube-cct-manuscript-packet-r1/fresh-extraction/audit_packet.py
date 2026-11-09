from pathlib import Path
import hashlib,json,re,os,sys
P=Path(__file__).resolve().parent;F=P/'formal'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((F/'pins.json').read_text())
lean=Path(os.environ.get('CUBE_LEAN','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))
mf=Path(os.environ.get('CUBE_LAKE_MANIFEST',pins['manifest_original']))
packages=Path(os.environ.get('CUBE_PACKAGES',str(mf.parent/'.lake/packages')))
assert sha(lean)==pins['lean_sha256'];assert sha(mf)==pins['manifest_sha256']
heads={}
for pin in pins['packages']:
 p=packages/pin['name'];g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  ref=h[5:]
  h=(g/ref).read_text().strip() if (g/ref).exists() else next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+ref))
 assert h==pin['rev'];heads[pin['name']]=h
assert all(sha(F/n)==h for n,h in json.loads((F/'source-manifest.json').read_text()).items())
if '--pins-only' in sys.argv:print('Compiler, manifest, nine packages and immutable sources PASS');sys.exit()
log=(F/'Audit.log').read_text();assert '⋯' not in log
records=[]
for block in re.split(r'(?=^DECL\|)',log,flags=re.M):
 if not block.strip():continue
 m=re.match(r'DECL\|([^\n]+)\|ORIGIN\|(Finite|Cube|Endpoint)\|UNSAFE\|false\nSAFETY\|([^\n]+)\|([^\n]+)\n',block)
 assert m,block[:100]
 name,origin,name2,safety=m.groups();assert name==name2 and safety in ['nondefinition','Lean.DefinitionSafety.safe']
 a=re.search(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",block,re.M);assert a and a[1]==name
 typ=block[m.end():a.start()].strip();assert typ.startswith(name) and ':' in typ
 axioms=[x.strip() for x in re.sub(r'\.\{[^}]+\}','',a[2] or '').split(',') if x.strip()]
 assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
 records.append({'name':name,'origin':origin,'safety':safety,'axioms':axioms,'type':typ,'type_sha256':hashlib.sha256(typ.encode()).hexdigest()})
assert len(records)==134 and len({r['name'] for r in records})==134
assert {k:sum(r['origin']==k for r in records) for k in ['Finite','Cube','Endpoint']}=={'Finite':92,'Cube':10,'Endpoint':32}
assert next(r['type'] for r in records if r['name']=='Cube.literal_question66_false').endswith('Not Cube.LiteralQuestion66AtFive')
for mod in ['Finite','Cube','Endpoint','Audit']:
 r=json.loads((F/(mod+'.guard.json')).read_text());assert r['exit_code']==0 and r['reason'] is None
 assert r['sampled_peak_group_rss']<=2800*1024**2
out={'status':'PASS','count':134,'partial_definitions':[],'package_heads':heads,'records':records,'audit_sha256':sha(F/'Audit.log')}
(P/'actual-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 134 full actual types, safe, no partials, Std3; endpoint closed; all pins unchanged')
