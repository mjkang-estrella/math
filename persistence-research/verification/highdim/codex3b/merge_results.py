"""Keep the strongest completed attempt and references to every checkpointed stage."""
import sys
sys.dont_write_bytecode=True
import pathlib,json,collections,os,copy
HERE=pathlib.Path(__file__).resolve().parent
share=json.load(open(HERE/'share.json'))['keys'];results=json.load(open(HERE/'results_t14112.json'))
assert set(results)==set(share),(len(results),len(share))
full_names={'escalation_minimal','promote_dim4','old300','adaptive60','adaptivecheap60','promote_final'}
stages={p.name:json.load(open(p)) for p in sorted(HERE.glob('stage_*.json'))}
for key in share:
 candidates=[results[key]];history=[]
 for fn,ss in stages.items():
  if key not in ss:continue
  a=ss[key];stage=a['stage']
  history.append({'file':fn,'key':key,'stage':stage,'scope':'configuration' if stage in full_names else 'first-slice probe','status':a['status'],'budget':a.get('budget'),'lifts_attempted':a.get('lifts_attempted'),'elapsed_s':a.get('elapsed_s'),'reason':a.get('stop_reason')})
  if stage in full_names:candidates.append(a)
 complete=[a for a in candidates if a['status']=='CLOSED']
 chosen=max(complete or candidates,key=lambda a:(a.get('lifts_attempted',0),a.get('budget',{}).get('seconds',0)))
 results[key]=copy.deepcopy(chosen);results[key]['attempt_history']=history
p=HERE/'results_t14112.json';tmp=str(p)+'.tmp';json.dump(results,open(tmp,'w'),indent=1);os.replace(tmp,p)
print('MERGED',dict(collections.Counter(x['status'] for x in results.values())))
