import json,hashlib,gzip,datetime
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;cwd=B.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((P.parent/'root-edge-irregulator-review-freeze-r1/review-freeze.json').read_text())
src=Path(freeze['source_lane'])
assert all(sha(src/name)==h for name,h in freeze['files'].items())
review=P.parent/'sol-edge-irregulator-preliminary-review-r1'
reviewhashes={str(f.relative_to(review)):sha(f) for f in sorted(review.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}
records=json.loads((P/'CURRENT-REGISTRIES.json').read_text())
for repo in ('omega','openai'):
 f=P/(repo+'-tree.txt');assert sha(f)==records[repo]['tree_sha256']
 with open(P/(repo+'-tree.txt.gz'),'wb') as out:
  with gzip.GzipFile(fileobj=out,mode='wb',mtime=0,filename='') as z:z.write(f.read_bytes())
note={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'credit':0,'counts':[7,37],'decision':'Adopt preliminary ordinary math and scoped substantive PASS; defer formal investment pending focused current-prior adjudication.','candidate_hashes_verified':len(freeze['files']),'review_files':reviewhashes,'review_provenance_qualification':'Reviewer did not supply standalone provenance.json; review.md embeds source/URL/UTC/hashes and live/ contains receipts. This inventory binds actual deliverables, not an invented file.','freshness_progress':'Public Git smart HTTP recovered complete inventories and selected actual bodies at recorded heads; no API retry or bypass. Current focused review pending. Complete inventory is not full body review.','failures':records['failures'],'source_qualification':'Author-deposited WALCOM2026 manuscript exact assertion verified; publisher-certified wording not acquired.','active_review':'sol-edge-irregulator-current-prior-review-r2'}
(P/'ADOPTION.json').write_text(json.dumps(note,indent=2)+'\n')
nf=B/'NEXT.md';text=nf.read_text()
text=text.replace('review in sol-edge-irregulator-preliminary-review-r1 is pending. Credit0.','review confirms ordinary math and scoped substantive PASS. Current-prior r2\nreview is pending; no formal investment or credit yet. Root public Git reads\nrecovered complete current Omega70af5407/OpenAI7ef5c0cc inventories, recorded in\nroot-edge-irregulator-current-prior-r1/CURRENT-REGISTRIES.json. Old API freshness\nlimits are historical; these are new dated inventories, not global priority proof.')
text=text.replace('Active Sol high/default: edge-irregulator review, fresh arithmetic/algebra r73,','Active Sol high/default: edge-irregulator current-prior r2, fresh arithmetic/algebra r73,')
nf.write_text(text)
paths=[]
for folder in (review,P):
 for f in sorted(folder.rglob('*')):
  if not f.is_file() or any(part.endswith('.git') or part=='__pycache__' for part in f.parts):continue
  if f.parent==P and f.name in ('omega-tree.txt','openai-tree.txt','pathspec.txt'):continue
  paths.append(str(f.relative_to(cwd)))
paths.append(str(nf.relative_to(cwd)))
(P/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'freeze':len(freeze['files']),'review_files':len(reviewhashes),'selected_paths':len(paths),'heads':{k:records[k]['head'] for k in ('omega','openai')}}))
