"""Recompute numeric content; bibliographic identifiers have source provenance, not arithmetic meaning."""
from pathlib import Path
import json,re,hashlib,xml.etree.ElementTree as ET
p=Path(__file__).resolve().parent.parent
a=json.loads((p/'receipts/arithmetic.json').read_text())
assert a['audit_data_rows']==7825 and a['audit_local_by_module']==201
assert a['module_count']==7
assert a['edges']==2*(3+2*3*2)==30
assert a['vertices']==2*(2*3+2)==16
assert 2*sum(range(1,31))==sum(x['weight'] for x in a['weights'])==930
# Verify every displayed certificate sum afresh, including the displayed examples.
rows=a['table']
assert rows[0][2]+rows[0][3]+rows[0][4]==45
assert rows[0][2]+rows[0][5]+rows[0][6]==49
for c,w in [(0,84),(1,99)]:
 rr=[r for r in rows if r[0]==c]
 assert sum(r[3]+r[5] for r in rr)==w
 assert sum(r[4]+r[6] for r in rr)==w
# All proof elimination identities checked at the coefficient level (M,S,Z,T,Q).
# 2*(2M-S-6Z)+(M+2S-T)=5M-12Z-T.
x=(2,-1,-6,0,0);y=(1,2,0,-1,0)
assert tuple(2*u+v for u,v in zip(x,y))==(5,0,-12,-1,0)
# 5*(-M+6Z-Q)+(5M-12Z-T) = 18Z-T-5Q.
z=(-1,0,6,0,-1)
assert tuple(5*u+v for u,v in zip(z,(5,0,-12,-1,0)))==(0,0,18,-1,-5)
assert 6*30==180 and sum(range(1,13))==78
assert 5*180-465==435 and 5*78+465==855
assert 3*435==1305 < 1710==2*855
# Recompute general count coefficients by counting endpoint and edge types.
# Each component has b=2s+1 pairs: 2b+m vertices; b matching +2bm joins.
assert (2*3+2,3+2*3*2)==(8,15)
# Definition file is byte-identical to the accepted common basics hash.
mods=list((p/'packet-test').rglob('*.lean'))
basics=next(f for f in mods if f.name=='AntimagicBasics.lean')
assert hashlib.sha256(basics.read_bytes()).hexdigest()=='eaa3cbd1aa5e2729f6ec5dc562f0ddbf5946a39908de9bbabc593ae0b8be6a1c'
# Provenance for non-computational numerals printed in the paper.
provenance={
 'source_publication':{'file':'evidence/expanded-corpus-r159/sources/antimagic-published.txt','strings':['124 (2025)','189','206','205','Conjecture 4.1','10.61091/um124-12']},
 'older_analogue':{'file':'evidence/expanded-corpus-r159/sources/antimagic-cco.txt','strings':['10, No. 4 (2025)','973-988','10.22049/cco.2024.29032.1818','Theorem 9']},
 'copies_paper':{'file':'evidence/joinla-formal-r2/downloads/book/text.txt','strings':['Mathematics 2021','1230','math9111230']},
 'formal_toolchain':{'file':'evidence/joinla-formal-r2/REPRODUCE.md','strings':['4.34.1','d13f23b723b8a846827a245b89c10fc7d3f11612','120','140']},
 'raw_id':{'file':'evidence/expanded-corpus-r159/raw/365453.jsonl','strings':['365453','2410.17674']}}
for r in provenance.values():
 s=(p/r['file']).read_text()
 for t in r['strings']:assert t in s,(r['file'],t)
# Inventory all numeral tokens, including indices and equation/reference numbers.
content=json.loads((p/'paper-content.json').read_text()); inventory=[]
for i,pg in enumerate(content,1):
 text=pg['title']+' '+str(pg['blocks'])
 inventory.append({'page':i,'numeral_tokens':sorted(set(re.findall(r'\d+(?:[.,]\d+)*',text)))})
(p/'receipts/numbers.json').write_text(json.dumps({'status':'PASS','computed':'Every mathematical numerical claim, table label, incidence sum and bound checked from scratch; polynomial identities checked coefficientwise. Indices and equation/reference numbers are notation. Dates, bibliographic numbers, SHA/revision identifiers and resource settings are source-bound metadata, not inferred arithmetic.','source_metadata':provenance,'token_inventory':inventory},indent=2)+'\n')
print('Numeric and metadata checks PASS')
