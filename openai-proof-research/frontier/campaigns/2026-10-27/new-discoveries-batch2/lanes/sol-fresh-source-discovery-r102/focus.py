from pathlib import Path
import json,re,urllib.request,hashlib,datetime
P=Path(__file__).resolve().parent;R=next(x for x in P.parents if x.name=='openai-proof-research');B=P.parent.parent
# Save context identities and family/status contents, not only timestamps.
rows=[]
for f in [R/'AGENTS.md',B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md',P.parent/'root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json',B/'discrete-r4-failure-recovery.json']:
 b=f.read_bytes();rows.append(dict(file=str(f),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
(P/'context-read.json').write_text(json.dumps(rows,indent=2))
a=json.loads((P/'duplicate-audit.json').read_text());(P/'duplicate-audit-second.json').write_text(json.dumps(a,indent=2))
terms=re.compile(r'2610.34990|Saturation numbers of.*P|clique.path.saturat|Zhang.*You.*Zhao|Li.*You.*Zhang|minimal.*fort|fort.*abundance|2512.12874|2609.11754',re.I)
hits=[]
for row in a['files']:
 f=R/row['path'];b=f.read_bytes()
 for i,l in enumerate(b.decode(errors='replace').splitlines(),1):
  if terms.search(l):hits.append(dict(path=row['path'],line=i,text=l[:2500]))
(P/'duplicate-audit-focus.json').write_text(json.dumps(dict(terms=terms.pattern,files=a['files'],hits=hits),indent=2));print('focus hits',json.dumps(hits),flush=True)
# Fresh target-body comparison in baseline + r99 inherited deltas; earlier r101 delta already read separately.
terms2=re.compile(r'saturat|CliquePath|PathJoin|fort',re.I);paths=[]
f=P.parent/'root-edge-irregulator-final-freeze-r1/omega-tree.txt'
for l in f.read_text().splitlines():
 path=l.split('\t')[-1]
 if ('Blueprint/D5/S3/Combinatorics/Graph/Saturation/' in path and path.endswith('.md')) or path=='Library/GraphInvariants/wangtian2026strongsaturation.md':paths.append(path)
log=json.loads((P/'http.json').read_text());h=json.loads((P/'sources/omega-head.json').read_text())['sha']
for i,path in enumerate(paths):
 u='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+path
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read();status=r.status
  n='sources/saturation-registry-'+str(i)+'.txt';(P/n).write_bytes(b);log.append(dict(url=u,status=status,file=n,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));print(path,b.decode()[:850],flush=True)
 except Exception as e:log.append(dict(url=u,error=str(e)))
(P/'http.json').write_text(json.dumps(log,indent=2))
