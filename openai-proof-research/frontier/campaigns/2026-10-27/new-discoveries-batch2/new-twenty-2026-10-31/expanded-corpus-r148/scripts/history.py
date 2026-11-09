import pathlib,json,hashlib,re
L=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((L/'reservation.json').read_text())['rows'];(L/'outputs/titles.txt').write_text('\n'.join(r['title'] for r in rows)+'\n')
# Read both ledgers, preserving exact family records but printing only their keys and candidate IDs.
for f in [L.parents[1]/'ledger.json',L.parent/'ledger.json',L.parents[1]/'prior-campaign-context.json']:
 o=json.loads(f.read_text()); print(f.name,hashlib.sha256(f.read_bytes()).hexdigest(),list(o))
 for k in ['accepted','accepted_results','excluded_after_review','completed','results']:
  if k in o:
   v=o[k]; print(k,'count',len(v));print(str(v)[:1000])
for i,v in json.loads((L/'outputs/provenance.json').read_text()).items():v['statement_sha256']=hashlib.sha256(v['record']['statement'].encode()).hexdigest()
