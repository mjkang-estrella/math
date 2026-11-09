import pathlib,json,re,hashlib,subprocess
p=pathlib.Path.cwd();batch=p.parents[1];ids=json.loads((p/'reservation.json').read_text())['ids'];o={}
for f in [batch/'ledger.json',batch/'prior-campaign-context.json',p.parent/'ledger.json']:
 if not f.exists():continue
 b=f.read_bytes();d=json.loads(b);o[str(f)]={'sha256':hashlib.sha256(b).hexdigest(),'top_level_keys':list(d),'matching_id_entries':[]}
 def walk(x):
  if isinstance(x,dict):
   if any(str(x.get(k)) in list(map(str,ids)) for k in ['mathdb_id','mathdb_related_id','id']):o[str(f)]['matching_id_entries'].append(x)
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(d)
 # Read and retain compact credited/excluded family data, without edits.
 o[str(f)]['family_summaries']=[{k:v for k,v in r.items() if k in ['title','mathdb_id','mathdb_related_id','status','reason','source_target']} for key in ['accepted','excluded','rejected','excluded_candidates'] for r in d.get(key,[]) if isinstance(r,dict)]
(p/'outputs/ledger-read.json').write_text(json.dumps(o,indent=2))
pat='|'.join(map(str,ids));r=subprocess.run(['rg','-n','-w',pat,str(batch),'--glob','*.md','--glob','!expanded-corpus-r156/**'],capture_output=True,text=True)
lines=[s for s in r.stdout.splitlines() if '/expanded-corpus-r156/' not in s];(p/'outputs/historical-exact-id-hits.txt').write_text('\n'.join(lines)+'\n');print('history exact MD hits',len(lines));print('\n'.join(s[:300] for s in lines[:10]))
