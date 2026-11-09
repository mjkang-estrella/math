import pathlib,hashlib,json,shutil,datetime
B=pathlib.Path(__file__).resolve().parents[2]
L=pathlib.Path(__file__).resolve().parent
S=B/'lanes/sol-wide-analytic-geometric-scout-r246'
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
names=['PROOF.md','FAILURES.md','provenance.json','SCOUTING.md','history-index.json','alias-history.json','diagnostics.py','diagnostics.json','RUN.md']
files=[S/n for n in names]
for v in ['v1','v2']:
 for typ in ['frozen','text-frozen']:
  files+=list((S/f'2307.00545{v}-{typ}').glob('*'))
files+=list((S/'sources').glob('*2307*'))
files+=list((S/'prior0-frozen').glob('*'))+list((S/'prior1-frozen').glob('*'))
files+=list((S/'current0-frozen').glob('*'))+list((S/'current1-frozen').glob('*'))+list((S/'current2-frozen').glob('*'))+list((S/'current3-frozen').glob('*'))
for p in files:
 if not p.is_file():continue
 q=L/'frozen'/p.relative_to(S);q.parent.mkdir(parents=True,exist_ok=True)
 a=h(p);shutil.copyfile(p,q);b=h(p);c=h(q);assert a==b==c
 records.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=a,kind='scientific'))
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']:
 if not p.exists():continue
 q=L/'administrative'/p.name
 if q.exists():q=L/'administrative'/'ancestor-AGENTS.md'
 q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
 records.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h(q),kind='administrative snapshot only'))
(L/'freeze-record.json').write_text(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=records),indent=2)+'\n')
print(json.dumps({'frozen':len(records),'files':[r['copy'] for r in records]}))
