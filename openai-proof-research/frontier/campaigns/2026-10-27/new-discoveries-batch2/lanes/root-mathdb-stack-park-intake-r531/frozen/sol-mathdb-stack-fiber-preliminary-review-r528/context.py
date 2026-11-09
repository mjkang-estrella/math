from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;L=D.parent;R=L.parents[4]
def rec(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
rows=json.loads((D/'flat-bindings.json').read_text());p=L/'pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0010.jsonl';rows.append(rec(p))
for q in [R/'sources/upstream.json',R/'sources/CONTENTS.md']:rows.append(rec(q))
(D/'flat-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
# Only extract assigned records, no other scientific statements.
selected=json.loads((D/'literal-records.json').read_text());lines=p.read_text().splitlines();out=[]
for x in selected:
 line=lines[x['corpus_line']-1];r=json.loads(line)
 out.append(dict(id=x['mathdb_id'],raw=r,statement_present=x['statement'] in str(r),line_sha256=hashlib.sha256(line.encode()).hexdigest()))
(D/'original-records.json').write_text(json.dumps(out,indent=2)+'\n')
t=json.loads((D/'n5-hand-traces.json').read_text());report=[]
for p,t in t.items():report.append(dict(input=p,moves=''.join('N' if z['action']=='push' else 'X' for z in t),output=''.join(str(z['element']) for z in t if z['action']!='push')))
(D/'trace-table.json').write_text(json.dumps(report,indent=2)+'\n')
(D/'context-output-bindings.json').write_text(json.dumps([rec(D/'original-records.json'),rec(D/'trace-table.json')],indent=2)+'\n')
print(json.dumps(report));print('upstream', (R/'sources/upstream.json').read_text()[:1200])
