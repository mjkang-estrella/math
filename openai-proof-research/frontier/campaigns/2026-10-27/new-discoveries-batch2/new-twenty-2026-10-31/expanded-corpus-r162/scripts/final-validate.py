import pathlib,json,hashlib,re,os,datetime,collections
D=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((D/'results.json').read_text())
groups=collections.defaultdict(list)
for i,o in rows.items():groups[o['provenance']['chunk']].append((i,o))
for path,rs in groups.items():
 p=pathlib.Path(path);data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==rs[0][1]['provenance']['chunk_sha256']
 lines=data.splitlines(keepends=True)
 for i,o in rs:assert lines[o['provenance']['line_1based']-1]==(D/f'raw/{i}.jsonl').read_bytes()
assert len(rows)==20
others=[]
for p in pathlib.Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:a=(p/'cmdline').read_bytes().split(b'\0');s=b' '.join(a).decode(errors='replace')
 except OSError:continue
 if str(D) in s and pathlib.Path(a[0].decode(errors='replace')).name in ['python3','python3.15','lean','leanchecker']:others.append((p.name,s[:500]))
assert not others,others
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_id_key_count':20,'chunk_hashes_rechecked':len(groups),'exact_raw_line_bindings_rechecked':20,'remaining_lane_heavy_processes':others,'accepted_credit':0,'root_review_required':True}
(D/'outputs/final-validation.json').write_text(json.dumps(report,indent=2))
# Logs for this validation are still being written, so exclude only those mutable receipts.
skip={'manifest.json','logs/final-validate.log','logs/final-validate.receipt.json'}
manifest={}
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in skip and p.suffix not in ['.olean','.ilean','.ir','.private','.server']:
  manifest[str(p.relative_to(D))]=hashlib.sha256(p.read_bytes()).hexdigest()
(D/'manifest.json').write_text(json.dumps(manifest,indent=2))
print(json.dumps(report,indent=2))
print('proof-source.zip SHA256',manifest['proof-source.zip'])
