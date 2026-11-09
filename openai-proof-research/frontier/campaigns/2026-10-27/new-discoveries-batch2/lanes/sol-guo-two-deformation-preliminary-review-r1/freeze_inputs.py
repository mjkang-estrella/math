from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-sun-odd-power-full-r1'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
items=[S/'pivot-proof.md',S/'report.md',S/'FAILURES.md',S/'http.jsonl',S/'freeze.json',S/'retrieved-freeze.json']
for name in ['schilling-warnaar','divisibility','guoschlosser','microscope','maopan','factors']:
 for ext in ['pdf','txt']:items.append(S/'retrieved-frozen'/f'{name}.{ext}')
rows=[]
items += [S/'frozen'/'sun.txt', S/'frozen'/'sun.pdf', S/'retrieved-frozen'/'factors-abs.html']
for p in items:
 if not p.exists():continue
 dest=L/'frozen'/p.relative_to(S);dest.parent.mkdir(parents=True,exist_ok=True)
 before=h(p);shutil.copyfile(p,dest);assert h(p)==h(dest)==before
 rows.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=before))
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']:
 if not p.exists():continue
 d=L/'administrative'/p.name;d.parent.mkdir(exist_ok=True);shutil.copyfile(p,d)
ledger=json.loads((B/'ledger.json').read_text())
prior=json.loads((B/'prior-campaign-context.json').read_text())
(L/'freeze.json').write_text(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),scientific=rows,administrative='snapshots only; not required stable against root updates',counts={k:ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']},prior_context_keys=list(prior)),indent=2)+'\n')
print(json.dumps({'frozen':len(rows),'counts':{k:ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']},'prior_keys':list(prior)}))
