import json,pathlib,hashlib,re
L=pathlib.Path(__file__).resolve().parents[1];rs=json.loads((L/'reservation.json').read_text())['rows'];terms=[str(r['mathdb_id']) for r in rs]+[r['source_url'].split('/')[-1] for r in rs]+['Vargas','Waldron','Narayan','Knill','Banica','Chirvasitu','Bian','Defant','Kravitz','Long','Wagner','Alishahi','Dowlin','Allem','Molina','Pastine','Alexandr','Burks','Chepuri','Commins','Liang','Van Name','Dross','Havet','Gu','Huang','Sun','Lau','Shiu','Premalatha','Nalliah','Skoviera','Škoviera','Macajova','Máčajová','Merzon','Smirnov','Codenotti','Riccardi','Venturello','Ferrara','Przyjalkowski','Shramov','Alexandrov','Buryak','Tessler']
p=re.compile('|'.join(re.escape(s) for s in terms),re.I);hits={}
for f in (L/'http').glob('poolraw-*/body'):
 hits[f.parent.name]=[{'line':i,'text':s} for i,s in enumerate(f.read_text().splitlines(),1) if p.search(s)]
(L/'registry-exact-author-screen.json').write_text(json.dumps({'terms':terms,'hits':hits,'limitation':'Author substrings cause false positives; candidate index and repository paths are bounded screens, not worldwide absence proofs.'},indent=2))
# Source locations and all printed labelled example/figure captions for counterexample comparison.
source={}
for f in (L/'texts').glob('*.txt'):
 lines=f.read_text().splitlines();sn=[];fig=[]
 for i,s in enumerate(lines):
  if re.search(r'(Conjecture|conjecture|Question)\s+\d|Conjecture [A-D][. ]',s):sn.append({'line':i+1,'context':'\n'.join(lines[max(0,i-2):min(len(lines),i+9)])})
  if re.search(r'\b(Figure|Example|Table)\s+\d',s):fig.append({'line':i+1,'text':s})
 source[f.name]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'conjecture_locations':sn,'example_figure_table_mentions':fig}
(L/'source-locations.json').write_text(json.dumps(source,indent=2))
# exact provenance for all records and receipts, immutable HTTP body hashes.
o={}
for f in (L/'http').glob('*/receipt.json'):
 r=json.loads(f.read_text());r['receipt_sha256']=hashlib.sha256(f.read_bytes()).hexdigest();o[f.parent.name]=r
(L/'http-manifest.json').write_text(json.dumps(o,indent=2))
print('receipts',len(o),'denials',[(n,r.get('status')) for n,r in o.items() if r.get('status') in (403,429)],'author hits',sum(map(len,hits.values())))
