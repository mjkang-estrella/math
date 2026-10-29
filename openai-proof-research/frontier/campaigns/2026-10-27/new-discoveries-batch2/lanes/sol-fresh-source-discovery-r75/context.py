import pathlib,json,hashlib,re
lane=pathlib.Path(__file__).resolve().parent;root=lane.parents[5];batch=lane.parents[1]
# Read whole required JSON documents, recording every outcome's substantive scope.
out={}
for name in ['ledger.json','prior-campaign-context.json']:
 p=batch/name;b=p.read_bytes();obj=json.loads(b);out[name]={'sha256':hashlib.sha256(b).hexdigest(),'keys':list(obj),'accepted':[{k:x[k] for k in ['number','title','scope','status','source_target'] if k in x} for x in obj['accepted']]}
print(json.dumps(out,indent=2,ensure_ascii=False))
