from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text());assert 'finalmanifest.json' not in m and 'verification-receipt.json' not in m
for p,sha in m.items():assert h(L/p)==sha,p
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']};assert actual==set(m)
bindings=json.loads((L/'frozenbindings.json').read_text())
for r in bindings:assert h(Path(r['original']))==h(Path(r['copy']))==r['sha256'],r['original']
retrieval=[json.loads(s) for s in (L/'retrieval.jsonl').read_text().splitlines()]
for r in retrieval:
 if 'sha256' in r:assert h(L/'primary'/r['name'])==r['sha256']
 if 'text_sha256' in r:assert h((L/'primary'/r['name']).with_suffix('.txt'))==r['text_sha256']
 # Failures retained, including truncated weighing source, are not treated as successes.
checks=json.loads((L/'checks.json').read_text());a=checks['rank19_coefficients']
assert checks['rank19_defects']==[a[i]**2-a[i-1]*a[i+1] for i in range(1,9)] and min(checks['rank19_defects'])>0
a=checks['public_counterexample']['coefficients'];assert a[2]**2-a[1]*a[3]==-3618068002504704
# Certify that the published column prescription is a literal rank-ten binary matroid.
cols=[v for v in range(1,1024) if not (v<8 or (v&7==0 and v>>9&1))];assert len(cols)==952
basis=[1<<i for i in range(3,9)]+[(1<<i)|(1<<3) for i in range(3)]+[1|(1<<9)]
assert all(v in cols for v in basis)
piv={}
for x in basis:
 while x:
  k=x.bit_length()-1
  if k not in piv:piv[k]=x;break
  x^=piv[k]
assert len(piv)==10
history=json.loads((L/'history-bindings.json').read_text());changed=[r['path'] for r in history if not Path(r['path']).exists() or h(Path(r['path']))!=r['sha256']]
# Other agents may update their own compact reports; record rather than silently bless it.
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(L/'finalmanifest.json'),'manifest_files':len(m),'manifest_pass':True,'frozen_original_copy_bindings':len(bindings),'frozen_original_copy_pass':True,'download_hashes_pass':True,'rank19_exact_lc':True,'public_counterexample_exact_determinant':True,'public_matroid_column_count':952,'public_matroid_rank':10,'full_flat_lattice_recomputed':False,'historical_reports_changed_after_binding':changed,'history_screen_limit':'compact lexical reports, not semantic clearance; any changed reports retain only pre-read binding evidence','credit':0,'counts_unchanged':'9 additional /39 total /next40'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
