import pathlib,json,urllib.request,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1]; out=[]
for repo in ['openai/math','the-omega-institute/trureturing']:
 url=f'https://api.github.com/repos/{repo}/commits/HEAD'
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check'}),timeout=15) as f:b=f.read();status=f.status
  fn=repo.replace('/','-')+'-head.json';(D/'sources'/fn).write_bytes(b)
  out.append(dict(url=url,status=status,sha256=hashlib.sha256(b).hexdigest(),head=json.loads(b)['sha'],utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:out.append(dict(url=url,error=str(e)))
(D/'sources/registry-receipts.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
# Read full ledgers, retaining concise family summaries locally.
B=D.parent.parent
for f in [B/'ledger.json',D.parent/'ledger.json',B/'prior-campaign-context.json']:
 o=json.loads(f.read_text()); (D/'outputs'/('context-'+f.parent.name+'-'+f.name)).write_text(json.dumps(o,indent=2))
# Avoid huge registry blobs mistaken for ID history by limiting matched lines.
lines=(D/'history-matches.txt').read_text().splitlines()
(D/'outputs/history-readable.txt').write_text('\n'.join(x for x in lines if len(x)<3000)+'\n')
