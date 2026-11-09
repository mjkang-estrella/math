import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];p=L.parent/'ledger.json';x=json.loads(p.read_text())
print('ledger keys:',list(x))
print('Accepted families:', '; '.join(str(i.get('mathdb_id'))+' '+str(i.get('title','')) for i in x.get('accepted',[])))
ids=json.loads((L/'reservation.json').read_text())['ids']
hits={}
def walk(o,path=''):
 if isinstance(o,dict):
  for k,v in o.items():
   if k in map(str,ids):hits[path+'/'+k]=v
   walk(v,path+'/'+k)
 elif isinstance(o,list):
  for i,v in enumerate(o):
   if isinstance(v,dict) and v.get('mathdb_id') in ids:hits[path+'/'+str(i)]=v
   walk(v,path+'/'+str(i))
walk(x);(L/'evidence/ledger-reserved-hits.json').write_text(json.dumps(hits,indent=2));print('Reserved ID hits',len(hits))
