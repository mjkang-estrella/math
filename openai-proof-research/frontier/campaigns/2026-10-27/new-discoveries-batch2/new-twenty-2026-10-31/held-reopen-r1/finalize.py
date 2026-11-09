import pathlib,json,hashlib,re,datetime
L=pathlib.Path(__file__).parent;B=L.parent
# Full line-context inventory also covers receipt formats that are not JSON.
paths=[s.split('  ',1)[1] for s in (L/'inputs-before.sha256').read_text().splitlines()]
with (L/'prior-route-text-excerpts.txt').open('w') as out:
 for p in paths:
  q=B/p
  if not any(s in p.lower() for s in ['receipt','fetch.log','fetch-r1.log','access','source-comparison']):continue
  if q.suffix not in ['.json','.jsonl','.md','.log','.txt']:continue
  try:t=q.read_text()
  except (UnicodeError,OSError):continue
  lines=t.splitlines()
  for n,s in enumerate(lines):
   if 'http://' in s or 'https://' in s:
    out.write(f'{p}:{n+1}\n'+'\n'.join(lines[max(0,n-1):min(len(lines),n+3)])+'\n\n')
# Input hashes re-read, never write into candidate lanes.
after=[];mismatch=[]
for row in (L/'inputs-before.sha256').read_text().splitlines():
 h,p=row.split('  ',1);q=B/p
 a=hashlib.sha256(q.read_bytes()).hexdigest()
 after.append(a+'  '+p)
 if a!=h:mismatch.append(p)
(L/'inputs-after.sha256').write_text('\n'.join(after)+'\n')
(L/'integrity.json').write_text(json.dumps({'checked':len(after),'mismatches':mismatch,'scope':'all files in named candidate/review/dossier lanes plus explicitly read ancestor and corpus/toolchain inputs; initial snapshot after introductory reads, before new network/replay; cache imports trusted'},indent=2))
print('hashes',len(after),'mismatches',mismatch)
