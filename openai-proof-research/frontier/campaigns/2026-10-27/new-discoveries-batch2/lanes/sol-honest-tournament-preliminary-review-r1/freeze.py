import pathlib,hashlib,json,shutil,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-wide-finite-arithmetic-mechanisms-r260'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for name in ['PROOF.md','witness-table.csv','primary-sources.json','tournamentprior.json','failures.md','retrieval.jsonl','SCOUTING.md']:
 p=S/name;q=L/'frozen'/name;q.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p);shutil.copyfile(p,q);assert sha(p)==h==sha(q)
 rows.append(dict(original=str(p),copy=str(q),sha256=h))
for p in (S/'frozen').iterdir():
 if p.is_file():
  q=L/'frozen'/'primary'/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  h=sha(p);shutil.copyfile(p,q);assert sha(p)==h==sha(q)
  rows.append(dict(original=str(p),copy=str(q),sha256=h))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 p=B/name;q=L/'administrative'/name;q.parent.mkdir(exist_ok=True)
 shutil.copyfile(p,q)
rows.append({'administrative_policy':'snapshot only; not scientific bindings'})
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
(L/'freeze-time.txt').write_text(datetime.datetime.now(datetime.timezone.utc).isoformat()+'\n')
print('Frozen',len(rows)-1,'scientific inputs; administrative snapshots copied')
