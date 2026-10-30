import pathlib,json,hashlib,datetime,shutil,sys
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'); L=B/'lanes/sol-pendulum-investment-review-r3'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
F=[B/'lanes/root-r166-preliminary-freeze-r1/review-freeze.json',B/'lanes/root-pendulum-published-source-adoption-r2/review-freeze.json']
if __name__=='__main__' and sys.argv[1]=='before':
 rows=[]
 for i,f in enumerate(F):
  data=json.loads(f.read_text()); shutil.copyfile(f,L/f'freeze-{i}.json')
  for r in data['files']:
   p=pathlib.Path(r['path']); assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
   q=L/'copies'/p.relative_to(B);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
   assert sha(q)==r['sha256'];rows.append(dict(r,copy=str(q)))
 (L/'before-freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows,'counts':[len(json.loads(f.read_text())['files']) for f in F]},indent=2))
 print('VERIFIED',len(rows))
elif __name__=='__main__' and sys.argv[1]=='inventory':
 for p in sorted((L/'copies').rglob('*')):
  if p.is_file() and (p.suffix=='.md' or any(s in p.name for s in ['coverage','provenance','retrieval','patch','tree','supplement'])):print(p.relative_to(L),p.stat().st_size)
elif __name__=='__main__' and sys.argv[1]=='after':
 d=json.loads((L/'before-freeze.json').read_text())
 for r in d['files']:
  for p in [pathlib.Path(r['path']),pathlib.Path(r['copy'])]: assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
 for i,f in enumerate(F):assert sha(f)==sha(L/f'freeze-{i}.json')
 for r in json.loads((L/'supplementary-input-checks.json').read_text()):
  assert sha(pathlib.Path(r['original']))==r['sha256']==sha(L/r['copy'])
 pr=json.loads((L/'provenance.json').read_text());assert sha(pathlib.Path(pr['guard']['path']))==pr['guard']['sha256']
 root=json.loads((L/'research/omega-root.json').read_text());problems=json.loads((L/'research/problems.json').read_text())
 assert next(r['sha'] for r in root['tree'] if r['path']=='Problems')==problems['sha']
 (L/'after-freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verified_original_and_copy_records':len(d['files']),'mismatches':[]},indent=2))
 rows=[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(L.rglob('*')) if p.is_file() and p.name!='final-verified-manifest.json']
 for r in rows:assert sha(L/r['path'])==r['sha256']
 (L/'final-verified-manifest.json').write_text(json.dumps({'files':rows,'verified':True},indent=2));print('FINAL VERIFIED',len(rows))
