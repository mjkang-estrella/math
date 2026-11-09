import pathlib,hashlib,json,datetime
R=pathlib.Path('/home/mj-kang/Documents/Dev/math'); C=R/'openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'; L=C/'lanes/sol-mathdb-primary-qualified-breadth-r470'
paths=[]
for name in ['root-mathdb-breadth-intake-r469','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 paths+=list((C/'lanes'/name).rglob('*'))
paths += [C/'ledger.json',C/'prior-campaign-context.json',R/'openai-proof-research/sources/upstream.json',R/'openai-proof-research/sources/CONTENTS.md',R/'openai-proof-research/sources/preprints-tree.json']
rows=[]
for p in sorted(set(paths)):
 if not p.is_file():continue
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b);n+=len(b)
 rows.append(dict(path=str(p.relative_to(R)),bytes=n,sha256=h.hexdigest()))
(L/'bindings.json').write_text(json.dumps(dict(frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),policy='Flat immutable references; hashed before scientific/history reading',files=rows),indent=2)+'\n')
print('Frozen',len(rows),'files',sum(x['bytes'] for x in rows),'bytes')
