from work import *
import re
idx=json.loads((L/'science/science--history-index.json').read_text())
refs=idx['verified_references']; out=[];hits=[]
terms=['2210.12842','2203.14815','1612.00862','2001.09248','2101.10023','1509.06540','1102.2723','1511.03658','1801.07238','2007.04668','2104.11971','1511.01246','1708.02857','1501.05922','Kneser','Madiman','Valent','Bahri','Cherny','Swanepoel','Godbersen']
for r in refs:
 p=pathlib.Path(r['path']); h=sha(p) if p.exists() else None
 out.append(dict(path=str(p),expected=r['sha256'],actual=h,match=h==r['sha256']))
 if h!=r['sha256']:continue
 t=p.read_text(errors='replace'); found=[s for s in terms if re.search(r'(?<![a-z])'+re.escape(s)+r'(?![a-z])',t,re.I)]
 if found:hits.append(dict(path=str(p),terms=found,excerpts=[t[max(0,t.lower().find(s.lower())-100):t.lower().find(s.lower())+450] for s in found]))
save(L/'history-verification.json',out);save(L/'history-hits.json',hits)
print(json.dumps(hits,indent=2)[:24000]);print('verified',sum(r['match'] for r in out),len(out))
