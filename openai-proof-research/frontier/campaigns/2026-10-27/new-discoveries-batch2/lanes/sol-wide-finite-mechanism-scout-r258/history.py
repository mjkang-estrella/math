from retrieve import *
import re
terms=['2002.01347','2002.01968','2002.02290','2002.02482','2002.02550','2102.00944','2102.01018','2102.01534','2102.02081','2102.03392','2202.00829','2202.01333','2202.02127','2202.04012','2202.11826','2202.12026','total roman','split overlap','centered flip','fixed row sum','toeplitz band','primary pseudo','twisted trace','idempotent evolution','associative-commutative','zinbiel','positive-definite matrices over finite','primitive element pairs']
hits={t:[] for t in terms};refs=[]
for p in sorted((B/'lanes').glob('*/*')):
 if p.parent==L or p.name.lower() not in ['summary.md','scouting.md','discovery.md','findings.md','decision.md']:continue
 h=sha(p);s=p.read_text(errors='replace').lower();assert sha(p)==h
 refs.append({'path':str(p),'sha256':h,'bytes':p.stat().st_size})
 for t in terms:
  if t in s:hits[t].append(str(p))
(L/'history-bindings.json').write_text(json.dumps(refs,indent=2));(L/'history-hits.json').write_text(json.dumps(hits,indent=2))
print(json.dumps(hits,indent=2));print('REPORTS',len(refs))
for p in [L/'administrative'/B.relative_to(ROOT)/'ledger.json',L/'administrative'/B.relative_to(ROOT)/'prior-campaign-context.json']:
 j=json.loads(p.read_text());print(p.name,'keys',list(j));
 for k,v in j.items():
  if isinstance(v,list):
   print(k,json.dumps(v)[:22000])
