import json,pathlib,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];C=D.parent
out={}
for p in [C/'ledger.json',C.parent/'ledger.json',C.parent/'prior-campaign-context.json',pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')]:
 data=p.read_bytes();out[str(p)]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
 if p.suffix=='.json':
  obj=json.loads(data);out[str(p)]['keys']=list(obj) if isinstance(obj,dict) else None
  def walk(x):
   if isinstance(x,dict):
    if 'title' in x and any(k in x for k in ['credit','status','discovery_count_credit']):yield {k:x[k] for k in ['mathdb_id','title','status','credit','discovery_count_credit'] if k in x}
    for v in x.values():yield from walk(v)
   elif isinstance(x,list):
    for v in x:yield from walk(v)
  out[str(p)]['families']=list(walk(obj))
(D/'outputs/inherited-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
figs={}
for p in sorted((D/'sources').glob('*v*.txt')):
 if any(a in p.name for a in ['2607.00153','2607.26266','2607.26606','2606.24016']):
  s=p.read_text();figs[p.name]=[s[max(0,m.start()-50):m.start()+550] for m in re.finditer(r'Figure \d+[.:]|Example \d+[.]\d+',s)]
(D/'outputs/printed-examples.json').write_text(json.dumps(figs,indent=2)+'\n')
print('Inherited families:',[(path,len(x.get('families',[]))) for path,x in out.items()]);print('printed examples indexed',len(figs))
