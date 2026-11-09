import pathlib,json,hashlib,os
D=pathlib.Path(__file__).resolve().parents[1];h=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(r)==set(map(str,ids))
for i,x in r.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n') and h(b)==x['provenance']['raw_sha256'];assert h(x['statement'].encode())==x['provenance']['statement_utf8_sha256']
receipts=[]
for p in sorted((D/'sources').glob('*/receipt.json')):
 z=json.loads(p.read_text());b=p.with_name('body').read_bytes();assert h(b)==z['sha256'] and len(b)==z['bytes'];receipts.append(z)
(D/'outputs/http-receipts-index.json').write_text(json.dumps(receipts,indent=2))
versions=json.loads((D/'outputs/source-versions.json').read_text());nversions=sum(len(x['versions']) for x in versions.values())
replay=json.loads((D/'logs/lean-final-verified.receipt.json').read_text());assert replay['returncode']==0
log=(D/'logs/lean-final-verified.log').read_text();assert 'Audited 45 local declarations' in log and 'FRESH STRICT REPLAY AND EXPLICIT MODULE LEANCHECKER PASSED' in log;assert 'sorryAx' not in log
for p in (D/'lean').glob('*.lean'):
 assert not any(t in p.read_text() for t in ['sorry','admit','native_decide','ofReduceBool'])
active=[]
for p in pathlib.Path('/proc').glob('[0-9]*/cmdline'):
 try:
  args=p.read_bytes().split(b'\0')
  if int(p.parent.name)!=os.getpid() and any(str(D).encode() in a for a in args) and any(a.endswith(b'/limited.py') for a in args):active.append(int(p.parent.name))
 except (OSError,ValueError):pass
assert not active,active
result={'id_count':len(r),'http_receipts_verified':len(receipts),'source_version_pdfs':nversions,'raw_lines_hash_verified':20,'active_heavy_processes':active,'lean_strict_fresh_replay':True,'leanchecker_explicit_module':'Certificate','all_local_declarations_audited':45,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'accepted_credit':0,'scope':'Artifact integrity and Lean replay only; source, significance, novelty and root acceptance not certified.'}
(D/'outputs/final-audit.json').write_text(json.dumps(result,indent=2));print(result)
manifest={str(p.relative_to(D)):h(p.read_bytes()) for p in D.rglob('*') if p.is_file() and p.name!='manifest.json'}
(D/'outputs/manifest.json').write_text(json.dumps(manifest,indent=2))
