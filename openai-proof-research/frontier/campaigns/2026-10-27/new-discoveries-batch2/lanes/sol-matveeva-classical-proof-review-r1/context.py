from pathlib import Path
import hashlib,json,urllib.request,datetime
p=Path(__file__).resolve().parent;b=p.parent.parent;root=b.parents[3]
# b = batch directory
paths=[root/'AGENTS.md',b/'AGENTS.md',b/'NEXT.md',b/'ledger.json',b/'prior-campaign-context.json',b/'lanes/root-fresh-source-r100-r101-handbacks/ADOPTION.json',b/'lanes/sol-mmpp-survival-preliminary-review-r1/counting-exclusions.json',b/'lanes/root-gamma-level-acceptance-r1/ACCEPTANCE.md',b/'lanes/root-arcsinh-acceptance-r1/ACCEPTANCE.md',b/'lanes/pi-gamma-perspective-review-r2/review.md',b/'lanes/sol-fresh-source-discovery-r101/sources/omega-head.json',b/'lanes/sol-fresh-source-discovery-r101/sources/openai-head.json',b/'lanes/sol-fresh-source-discovery-r101/sources/omega-delta.json',b/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']
rows=[]
for i,f in enumerate(paths):
 if not f.exists():print('missing',f);continue
 data=f.read_bytes();dest=p/'context'/f'{i:02d}-{f.name}';dest.parent.mkdir(exist_ok=True);dest.write_bytes(data)
 rows.append({'original':str(f),'copy':str(dest.relative_to(p)),'sha256':hashlib.sha256(data).hexdigest()})
(p/'context-hashes.json').write_text(json.dumps(rows,indent=2))
for repo,name in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
 url=f'https://api.github.com/repos/{repo}/commits/HEAD'
 try:
  with urllib.request.urlopen(url,timeout=25) as f:data=f.read();status=f.status
  (p/'live'/f'{name}-head.json').write_bytes(data);j=json.loads(data)
  print(name,j['sha'],j['commit']['committer']['date'])
  (p/'live'/f'{name}-head-receipt.json').write_text(json.dumps({'url':url,'status':status,'sha256':hashlib.sha256(data).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'head':j['sha']},indent=2))
 except Exception as e:print(name,str(e))
