import pathlib,json,hashlib,datetime,os
R=pathlib.Path(__file__).resolve().parents[1];before=json.loads((R/'receipts/before.json').read_text())['hashes'];after={}
for lane in ['expanded-corpus-r73','collapsing-review-r1']:
 for p in sorted((R.parent/lane).rglob('*')):
  if p.is_file():after[str(p.relative_to(R.parent))]=hashlib.sha256(p.read_bytes()).hexdigest()
diff=[p for p in before.keys()|after.keys() if before.get(p)!=after.get(p)]
(R/'receipts/after.json').write_text(json.dumps({'utc':str(datetime.datetime.now(datetime.timezone.utc)),'hashes':after,'changed':diff},indent=2))
recs=[]
for p in (R/'receipts').glob('*.json'):
 try:
  d=json.loads(p.read_text())
  if 'cpu_cap' in d:recs.append(d)
 except ValueError:pass
(R/'outputs/resource-summary.json').write_text(json.dumps(dict(heavy_processes=len(recs),peak_private=max(d['peak_private'] for d in recs),max_wall=max(d['wall'] for d in recs),cgroup=False,sampled_private_guard=True,xdg_runtime_present='XDG_RUNTIME_DIR' in os.environ,hash_inputs_unchanged=not diff, original_file_bytes_unchanged=all(after.get(p)==h for p,h in before.items()), additions=[p for p in after if p not in before], modifications=[p for p in before if after.get(p)!=before[p]]),indent=2))
print('original modifications', [p for p in before if after.get(p)!=before[p]], 'additions',len([p for p in after if p not in before]))
