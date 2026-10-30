from pathlib import Path
import json,hashlib,datetime,re
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,o):
 p=L/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(o,indent=2)+'\n')
utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
pattern=re.compile(r'2610\.25661|factorial separation|Brocard|3499670|1009873805276|factorial gap|Obl[aá]th',re.I)
aliases=[];hits=[]
for r in json.loads((L/'inherited-aliases.json').read_text())['records']:
 p=Path(r['reference_absolute']);q=Path(r['canonical_copy']);expected=r['sha256']
 assert sha(q.read_bytes())==expected
 current=sha(p.read_bytes()) if p.exists() else None
 z=dict(reference_absolute=str(p),snapshot_reference=str(q),sha256=expected,current_sha256=current,qualification='inherited alias, not original or scientific premise')
 if current!=expected:
  if current is not None:
   dest=L/'alias-deltas'/sha(str(p).encode());dest.parent.mkdir(exist_ok=True);dest.write_bytes(p.read_bytes());z.update(snapshot_reference=str(dest),sha256=current)
  else:z['missing']=True
 aliases.append(z)
 if not z.get('missing'):
  s=Path(z['snapshot_reference']).read_text(errors='replace');ms=list(pattern.finditer(s))
  if ms:hits.append(dict(reference=str(p),excerpts=[s[max(0,m.start()-70):m.end()+130] for m in ms[:3]]))
save('alias-refresh.json',dict(utc=utc,records=aliases));save('alias-target-screen.json',dict(pattern=pattern.pattern,hits=hits))
indexes=[]
for lane in ['sol-fresh-source-discovery-r207','sol-fresh-source-discovery-r208']:
 for p in (L.parent/lane/'indexes').iterdir():
  if p.is_file():
   q=L/'indexes'/(lane+'-'+p.name);q.write_bytes(p.read_bytes());indexes.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=sha(q.read_bytes()),qualification='historical index snapshot'))
save('index-bindings.json',indexes)
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';(L/'guard-copy.py').write_bytes(guard.read_bytes())
bindings=[json.loads(s)['binding'] for s in (L/'http.jsonl').read_text().splitlines() if 'binding' in json.loads(s)]
bindings.append(dict(original=str(guard),copy='guard-copy.py',sha256=sha(guard.read_bytes())))
for r in bindings:assert sha(Path(r['original']).read_bytes())==sha((L/r['copy']).read_bytes())==r['sha256']
save('scientific-bindings.json',dict(utc=utc,records=bindings,pre_read='Each successful HTTP body copied and verified in work.py fetch before extraction/read',post_read='all original/copy hashes checked here; separate final verifier repeats'))
retrievals=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
save('provenance.json',dict(utc=utc,status='UNRESOLVED_ZERO_NOMINATIONS',target=dict(title='The factorial separation conjecture',author='Valmir Krasniqi',arxiv='2610.25661v1',doi='10.48550/arXiv.2610.25661',submitted_utc='2026-10-19T02:08:37Z',statement='Conjecture1.1',scope='Every integer n>=8 and every pair of integers m,k>=2: abs(n!-m^k)>n'),retrievals=retrievals,scientific_bindings='scientific-bindings.json',history='qualified-original-index.json',aliases='alias-refresh.json',limits=['bounded search cannot clear all history','current complete public registries remain unauthenticated','MSE403 stopped without retry','No full ordinary source proof or refutation','No worldwide priority/unresolvedness claim'],missing_lemma='For every n>=8 and 1<=a^2<=n, n!/(4a^2) has no consecutive coprime factor pair; additionally exclude residual odd-prime-exponent prime displacements',counts=dict(additional=9,total=39,next=40,authority='root only'),manifest_exclusions=['finalmanifest.json','verification-receipt.json']))
excludes=['finalmanifest.json','verification-receipt.json']
save('finalmanifest.json',dict(utc=utc,exclusions=excludes,files={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excludes}))
print('finalized',len(bindings),'scientific bindings',len(aliases),'aliases',len(hits),'alias hits')
