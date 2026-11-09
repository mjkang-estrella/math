from pathlib import Path
import sys,json,hashlib,zipfile,subprocess,re,io,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
mode=sys.argv[1]
if mode=='pins':
 pins=json.loads((L/'pins.json').read_text());assert len(pins)==9
 for pin in pins:
  p=Path(pin['path']);g=p/'.git'
  if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
  head=(g/'HEAD').read_text().strip()
  if head.startswith('ref: '):
   ref=head[5:];r=g/ref;head=r.read_text().strip() if r.exists() else next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+ref))
  assert head==pin['revision'],pin
 compiler=sha(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))
 assert compiler=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
 save('pin-receipt.json',dict(status='PASS',compiler_sha256=compiler,pins=pins,package_count=9,changed=False))
 print('PASS compiler and nine package pins')
elif mode=='prepare':
 inherited=json.loads((L/'references/sol-fullerene-triple-certificates-formal-r3--mathematical-modules.json').read_text())
 oldorder=json.loads((L/'references/sol-fullerene-triple-certificates-formal-r3--replay-order.json').read_text())
 new=['FaceCore','FacetDimension','FacetStandard','IncidenceCore','PolygonCore','MinorCore','FeasibleG','FeasibleH']
 for t in ['G','H']:
  new += ['IncidenceData'+t,'IncidenceFacts'+t]+[f'Incidence{t}{i:02d}' for i in range(32)]+['IncidenceReal'+t]+[f'Facet{t}{i:02d}' for i in range(32)]+['Facets'+t,'Polygons'+t]
 audits=[]
 for i in range(0,len(new),12):
  name=f'AuditFacets{i//12:02d}';audits.append(name);mods=new[i:i+12]
  (L/(name+'.lean')).write_text('\n'.join(['import '+m for m in mods]+['import StrictAudit','#strict_audit ['+', '.join(mods)+']'])+'\n')
 save('mathematical-modules.json',inherited+new)
 save('replay-order.json',oldorder+new+audits)
 (L/'pins.json').write_bytes((L/'references/sol-fullerene-triple-certificates-formal-r3--pins.json').read_bytes())
 print(len(inherited+new),'mathematical modules;',len(oldorder+new+audits),'compiler calls')
elif mode=='archive':
 order=json.loads((L/'replay-order.json').read_text())
 files=[m+'.lean' for m in order]+['runner.py','pins.json','replay-order.json','mathematical-modules.json','RUN.md']
 save('archive-files.json',{f:sha(L/f) for f in files})
 with zipfile.ZipFile(L/'source.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
  for f in sorted(files+['archive-files.json']):
   i=zipfile.ZipInfo(f,(2026,10,30,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16;z.writestr(i,(L/f).read_bytes())
 D=L/'replay/fresh';D.mkdir(parents=True,exist_ok=False)
 with zipfile.ZipFile(L/'source.zip') as z:z.extractall(D)
 print(sha(L/'source.zip'))
elif mode=='replay':
 D=L/'replay/fresh';order=json.loads((D/'replay-order.json').read_text())
 for f,h in json.loads((D/'archive-files.json').read_text()).items():assert sha(D/f)==h,f
 for m in order[int(sys.argv[2]):int(sys.argv[3])]:
  r=subprocess.run([sys.executable,str(D/'runner.py'),'-o',m+'.olean',m+'.lean'],cwd=D,capture_output=True,text=True)
  print(m,r.returncode,flush=True)
  if r.returncode:print(r.stdout,r.stderr);sys.exit(r.returncode)
elif mode=='reconcile':
 D=L/'replay/fresh';order=json.loads((D/'replay-order.json').read_text());mods=set(json.loads((D/'mathematical-modules.json').read_text()))
 ok={};texts=[]
 for p in sorted(D.glob('attempt-*.json')):
  r=json.loads(p.read_text());s=p.with_suffix('.log').read_text();assert r['exit']==0 and r['reason'] is None,(p,r)
  assert not any(x in s.lower() for x in ['panic','error:','rejected','sorryax']),p
  ok[Path(r['command'][-1]).stem]=r;texts.append(s)
 assert set(ok)==set(order),set(order)-set(ok)
 text='\n'.join(texts);owned=set(re.findall(r'OWN_DECL (\S+)',text))
 covered=set(re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",text))
 assert owned==covered and owned,(owned-covered,covered-owned)
 for tag in ['OWN_SAFETY','OWN_PARTIAL']:
  rows=dict(re.findall(tag+r' (\S+) (\S+)',text));assert set(rows)==owned and set(rows.values())=={'false'}
 origins=set(re.findall(r'AUDITED_ORIGIN (\S+)',text));assert origins==mods,(mods-origins,origins-mods)
 observed=set()
 for s in re.findall(r'depends on axioms: \[([^\]]*)\]',text,re.S):observed|={x.strip() for x in s.split(',') if x.strip()}
 assert observed<={'propext','Classical.choice','Quot.sound'},observed
 inherited=set(json.loads((L/'references/sol-fullerene-triple-certificates-formal-r3--owned-declarations.json').read_text()));assert inherited<=owned
 save('owned-declarations.json',sorted(owned))
 save('audit.json',dict(status='PASS',owned=len(owned),origins=sorted(origins),private_generated=True,partial_flags=False,unsafe_flags=False,transitive_type_body_checked=True,axioms=sorted(observed),inherited_declarations_preserved=len(inherited)))
 save('replay-receipt.json',dict(status='PASS',archive_sha256=sha(L/'source.zip'),compiler_calls=len(order),owned=len(owned),serial=True,source_only=True,diagnostics_rejected=True))
 print('PASS',len(order),'calls',len(owned),'declarations')
elif mode=='finalize':
 assert json.loads((L/'replay-receipt.json').read_text())['status']=='PASS'
 for p in L.rglob('*'):
  if (p.is_file() or p.is_symlink()) and (p.suffix in ['.olean','.ilean','.o','.ir','.c'] or '.olean.' in p.name):p.unlink()
 failed=[]
 for p in sorted(L.rglob('attempt-*.json')):
  r=json.loads(p.read_text())
  if r['exit']!=0:failed.append(dict(receipt=str(p.relative_to(L)),accepted=False))
 save('failures.json',failed)
 save('provenance.json',dict(counts=dict(additional=9,total=39,next=40,changed=False),acceptance='root only',full_source='HOLD',novelty='HOLD',external_retrievals=[],inherited_modules_unchanged=True,archive_sha256=sha(L/'source.zip'),residual='Edges, adjacency, cubic primal incidence; no literal fullerene/fullSourceClaim'))
 save('MANIFEST.json',{str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']})
elif mode=='verify':
 manifest=json.loads((L/'MANIFEST.json').read_text());assert 'MANIFEST.json' not in manifest and 'verification-receipt.json' not in manifest
 assert set(manifest)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
 for f,h in manifest.items():assert sha(L/f)==h,f
 records=json.loads((L/'freeze.json').read_text())
 for r in records:
  assert sha(L/r['copy'])==r['sha256'],r
  if not r['copy'].startswith('references/admin--'):assert sha(Path(r['original']))==r['sha256'],r
 for m in json.loads((L/'references/sol-fullerene-triple-certificates-formal-r3--mathematical-modules.json').read_text()):
  assert sha(L/(m+'.lean'))==sha(L/('references/sol-fullerene-triple-certificates-formal-r3--'+m+'.lean')),m
 pins=json.loads((L/'pins.json').read_text());assert len(pins)==9
 for pin in pins:
  p=Path(pin['path']);g=p/'.git'
  if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
  head=(g/'HEAD').read_text().strip()
  if head.startswith('ref: '):
   ref=head[5:];r=g/ref;head=r.read_text().strip() if r.exists() else next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+ref))
  assert head==pin['revision'],pin
 assert sha(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
 assert not any(p.suffix in ['.olean','.ilean','.o','.ir','.c'] or '.olean.' in p.name for p in L.rglob('*') if p.is_file() or p.is_symlink())
 D=L/'replay/fresh'
 with zipfile.ZipFile(L/'source.zip') as z:
  for f in z.namelist():assert z.read(f)==(D/f).read_bytes(),f
 hashes=json.loads((D/'archive-files.json').read_text())
 for f,h in hashes.items():assert sha(L/f)==sha(D/f)==h,f
 buf=io.BytesIO()
 with zipfile.ZipFile(buf,'w',compression=zipfile.ZIP_DEFLATED) as z:
  for f in sorted(list(hashes)+['archive-files.json']):
   i=zipfile.ZipInfo(f,(2026,10,30,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16;z.writestr(i,(L/f).read_bytes())
 assert hashlib.sha256(buf.getvalue()).hexdigest()==sha(L/'source.zip')
 replay=json.loads((L/'replay-receipt.json').read_text());assert replay['status']=='PASS' and replay['archive_sha256']==sha(L/'source.zip')
 audit=json.loads((L/'audit.json').read_text());assert audit['status']=='PASS' and not audit['unsafe_flags'] and not audit['partial_flags']
 save('verification-receipt.json',dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'MANIFEST.json'),scientific_and_admin_bindings=len(records),compiler_calls=replay['compiler_calls'],owned=audit['owned'],counts_changed=False,exclusions=['MANIFEST.json','verification-receipt.json']))
 print((L/'verification-receipt.json').read_text())
