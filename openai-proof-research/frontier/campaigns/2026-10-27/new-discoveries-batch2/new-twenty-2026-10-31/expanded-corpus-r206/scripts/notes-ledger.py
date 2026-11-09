import json,pathlib,hashlib
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
out={}
for p in [B/'ledger.json',D.parent/'ledger.json',B/'prior-campaign-context.json']:
 obj=json.loads(p.read_text());out[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'keys':list(obj),'accepted_families':[{'id':a.get('mathdb_id',a.get('id')),'title':a.get('title',a.get('reason','')),'scope':a.get('scope',a.get('proposed_result',''))} for k in ['accepted','accepted_results','published_papers','held_candidates','excluded','rejected'] for a in obj.get(k,[]) if isinstance(a,dict)]}
(D/'outputs/inherited-family-read.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:len(v['accepted_families']) for k,v in out.items()})
