"""Read hash-distinct indexed texts with exact topic terms, bounded excerpts."""
import sqlite3,re,json,time
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
pats={
 'crown':re.compile(r'2504\.05123|crown.poset',re.I),
 'w2':re.compile(r'2605\.14076|2409\.00827|2.quasi.regular',re.I),
 'motzkin':re.compile(r'alternating.{0,25}Motzkin|A187306|19949645|aa55/aa55',re.I)}
counts={k:0 for k in pats}; examples={k:[] for k in pats};records=[];n=0
db=sqlite3.connect('file:'+str(L/'screen.sqlite')+'?mode=ro',uri=True)
start=time.monotonic()
for h,rel in db.execute('select h,path from bodies'):
    p=R/rel
    if not p.exists():continue
    # Never materialize a corpus. Bounded excerpt; read complete individual text.
    found={}
    with p.open(errors='replace') as f:
        for no,line in enumerate(f,1):
            for k,pat in pats.items():
                m=pat.search(line)
                if m and k not in found:
                    found[k]={'path':rel,'sha256':h,'line':no,'excerpt':line[max(0,m.start()-90):m.end()+300]}
    n+=1
    for k,v in found.items():
        counts[k]+=1
        if len(examples[k])<30:examples[k].append(v)
        if p.name in {'SUMMARY.md','discovery.md','review.md','DECISION.md'} or 'disposition' in p.name.lower():
            records.append(dict(topic=k,**v))
(L/'refined-screen.json').write_text(json.dumps({'bodies_read':n,'counts':counts,'bounded_examples':examples,'all_matching_disposition_records':records,'seconds':time.monotonic()-start},indent=2)+'\n')
print(n,counts,len(records))
