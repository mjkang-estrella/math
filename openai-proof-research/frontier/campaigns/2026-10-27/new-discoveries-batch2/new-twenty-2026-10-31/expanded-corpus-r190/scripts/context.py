import pathlib,json,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'outputs').glob('context-*'):
 x=json.loads(p.read_text());print(p.name)
 for k in ['accepted','excluded','excluded_after_review']:
  a=x.get(k,[])
  if isinstance(a,list):
   for z in a:print(k,z.get('mathdb_id',z.get('id')),z.get('title',z.get('reason',''))[:350])
ids=json.loads((D/'reservation.json').read_text())['ids']
r=subprocess.run(['rg','-l','--glob','*.md','--glob','results.json','--glob','!TASK.txt','--glob','!reservation.json','--glob','!ledger.json','|'.join(map(str,ids)),str(D.parent)],capture_output=True,text=True)
(D/'outputs/history-paths.txt').write_text(r.stdout);print('HISTORY',r.stdout[:6000])
