from pathlib import Path
import json,hashlib,datetime,re
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(n,o):(L/n).write_text(json.dumps(o,indent=2)+'\n')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
refs=[]
for lane,fn in [('sol-fresh-source-discovery-r210','alias-refresh.json'),('sol-fresh-source-discovery-r211','alias-refresh.json'),('sol-fresh-source-discovery-r209','alias-refresh.json')]:
 p=L.parent/lane/fn
 refs.append(dict(path=str(p),sha256=h(p),role='historical index snapshot'))
aliases={}
for r in refs:
 for a in json.loads(Path(r['path']).read_text())['records']:
  key=a.get('reference_absolute',a.get('original'))
  q=a.get('canonical_copy',a.get('snapshot_reference'))
  if key and q:aliases[key]=dict(original=key,snapshot_reference=q,sha256=a['sha256'])
pattern=re.compile(r'2610[.]40076|Del[ -]Donno|contact quanti[sz]ed flag|Reeb.{0,40}(D.?4|SO.?8)|nine.dimensional.{0,50}calculus|Dolbeault complex for the contact',re.I)
hits=[];changed=[]
for i,(key,a) in enumerate(sorted(aliases.items())):
 q=Path(a['snapshot_reference']);assert h(q)==a['sha256']
 p=Path(key)
 if p.is_file() and h(p)!=a['sha256']:
  z=L/'changed'/f'alias-{i}.md';z.write_bytes(p.read_bytes());a.update(snapshot_reference=str(z),sha256=h(z));changed.append(key)
 a['missing_current_original']=not p.is_file()
 a['qualification']='inherited alias only; never promoted to qualified-original provenance'
 text=Path(a['snapshot_reference']).read_text(errors='replace')
 if pattern.search(text):hits.append(dict(original=key,excerpts=[text[max(0,m.start()-70):m.end()+130] for m in list(pattern.finditer(text))[:4]]))
save('alias-refresh.json',dict(utc=utc(),records=list(aliases.values()),changed=changed))
save('alias-target-screen.json',dict(pattern=pattern.pattern,hits=hits))
for fn in ['qualified-original-index.json','history.json']:
 p=L.parent/'sol-fresh-source-discovery-r210'/fn
 if p.is_file():refs.append(dict(path=str(p),sha256=h(p),role='historical index snapshot'))
for r in json.loads((L/'qualified-original-index.json').read_text())['records']:
 if not r.get('missing'):refs.append(dict(path=r['snapshot_reference'],sha256=r['sha256'],role='qualified-original historical snapshot',original=r['original']))
for a in aliases.values():refs.append(dict(path=a['snapshot_reference'],sha256=a['sha256'],role='alias historical snapshot'))
assert all(h(r['path'])==r['sha256'] for r in refs)
save('reference-bindings.json',refs)
scientific=[]
for line in (L/'http.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'binding' in r:scientific.append(r['binding'])
g=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';c=L/'guard-copy.py';c.write_bytes(g.read_bytes())
scientific.append(dict(original=str(g),copy='guard-copy.py',sha256=h(g),utc=utc()))
for r in scientific:assert h(r['original'])==h(L/r['copy'])==r['sha256']
save('scientific-bindings.json',scientific)
save('provenance.json',dict(utc=utc(),status='unresolved; eligibility HOLD; zero nominations',
 target='Antonio Del Donno arXiv:2610.40076v1 abstract conjecture / Section 3.4',
 scientific_original_copy_bindings='scientific-bindings.json',external_snapshots='reference-bindings.json',
 administrative='ledger/NEXT/context snapshots only; never bound as live scientific premises',
 screen='1589 qualified originals plus separately refreshed inherited aliases; not exhaustive history',
 source_receipts='http.jsonl',counts_unchanged='9 additional / 39 total, next40; root alone decides',
 manifest_exclusions=['finalmanifest.json','verification-receipt.json']))
print(json.dumps(dict(qualified=1589,aliases=len(aliases),alias_hits=len(hits),changed_aliases=changed,
 actual_r111_113=[r['original'] for r in refs if 'original' in r and re.search(r'sol-fresh-source-discovery-r11[123]/',r['original'])]),indent=2))
