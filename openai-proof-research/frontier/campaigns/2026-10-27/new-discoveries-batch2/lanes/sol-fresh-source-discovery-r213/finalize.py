from pathlib import Path
import json,hashlib,datetime,re
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,o):(L/n).write_text(json.dumps(o,indent=2)+'\n')
pat=re.compile(r'2610\.03111|1201\.0622|Jacobi.Stirling|Gessel.{0,20}Lin.{0,20}Zeng|Ming.Xin Wang|2005\.06689|Plateaux on generalized Stirling|2610\.(38864|37522|36179|34772|29950|26535|26409|23495|22875|22151|17884|17798|20088|33653|21210)|Kalmanovich|Nivasch|\bRossi\b|height.rigid|G.stable Kneser|Stewart|symmetric two.counter|lattice Bruhat|hypohamiltonian',re.I)
refs=[];aliases={}
for lane in ['r209','r210','r211']:
 p=L.parent/('sol-fresh-source-discovery-'+lane)/'alias-refresh.json'
 # indexes themselves are snapshots, not live scientific premises
 q=L/'indexes'/('aliases-'+lane+'.json');q.write_bytes(p.read_bytes());refs.append(dict(path=str(q),sha256=sha(q.read_bytes())))
 for r in json.loads(q.read_text())['records']:
  key=r.get('reference_absolute',r.get('original'));aliases[key]=r
out=[];hits=[]
for key,r in sorted(aliases.items()):
 q=Path(r['snapshot_reference']);assert sha(q.read_bytes())==r['sha256']
 p=Path(key);cur=sha(p.read_bytes()) if p.is_file() else None
 if cur is not None and cur!=r['sha256']:
  q=L/'changed'/('alias-'+sha(key.encode())+'.md');q.write_bytes(p.read_bytes())
 h=sha(q.read_bytes());z=dict(reference_absolute=key,snapshot_reference=str(q),sha256=h,missing=cur is None,changed=cur!=r['sha256'],qualification='alias only, never promoted')
 out.append(z)
 s=q.read_text(errors='replace');m=list(pat.finditer(s))
 if m:hits.append(dict(reference=key,excerpts=[s[max(0,a.start()-70):a.end()+130] for a in m[:3]]))
save('alias-refresh.json',dict(utc=now(),records=out));save('alias-target-screen.json',dict(pattern=pat.pattern,hits=hits))
# Retain actual r111-113 qualified originals and verify canonical snapshots.
history=json.loads((L/'qualified-original-index.json').read_text())['records']
for r in history:
 if not r.get('missing'):assert sha(Path(r['snapshot_reference']).read_bytes())==r['sha256']
retained={n:[r['original'] for r in history if ('sol-fresh-source-discovery-r'+str(n)+'/') in r['original']] for n in [111,112,113]}
assert all(retained.values())
save('historical-coverage.json',dict(utc=now(),qualified=len(history),aliases=len(out),alias_hits=hits,retained_actual=retained,limits=['bounded canonical paths and top-level report refresh only','no parked historical intervals reopened','current complete public registry heads and bodies unauthenticated','no all-history clearance']))
for p in (L/'indexes').iterdir():
 if p.is_file():refs.append(dict(path=str(p),sha256=sha(p.read_bytes())))
save('index-bindings.json',refs)
bindings=[json.loads(t)['binding'] for t in (L/'http.jsonl').read_text().splitlines() if 'binding' in json.loads(t)]
p=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';q=L/'guard-copy.py';q.write_bytes(p.read_bytes());bindings.append(dict(original=str(p),copy='guard-copy.py',sha256=sha(q.read_bytes())))
for r in bindings:assert sha(Path(r['original']).read_bytes())==sha((L/r['copy']).read_bytes())==r['sha256']
save('scientific-bindings.json',dict(utc=now(),records=bindings,before='HTTP fetch writes original, copies and verifies both before extraction/read',after='Every original/copy pair checked after research, repeated by separate verifier'))
save('provenance.json',dict(utc=now(),status='UNRESOLVED_ZERO_NOMINATIONS',counts=dict(additional=9,total=39,next=40,authority='root only'),target=dict(original='Gessel-Lin-Zeng, arXiv1201.0622v2 Conjecture15',latest_close='Ma-Wang arXiv2610.03111v1 Theorem2 and Remark1',scope='every integer k>=1 and every 0<=i<=k, original numerator x*A[k,i](x) has only real roots'),retrievals=[json.loads(t) for t in (L/'http.jsonl').read_text().splitlines()],sources='scientific-bindings.json',history='historical-coverage.json',steering=dict(mode='BROAD_SCOUTING',triaged=16,ranked=5,register='scouting.json',shortlist='SCOUTING.md',retained_source_coverage='retained-sources.json',earlier_analysis='pre-steering-discovery.md',no_additional_diagnostics=True),exclusions=['finalmanifest.json','verification-receipt.json'],limits=['No complete ordinary proof/refutation','No exhaustive prior-art or public-unresolvedness certificate','No journal-version body comparison','No Lean/manuscript','RSS sampling does not exclude unsampled transients']))
exclude=['finalmanifest.json','verification-receipt.json']
save('finalmanifest.json',dict(utc=now(),exclusions=exclude,files={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclude}))
print('finalized',len(history),len(out),len(hits),len(bindings))
