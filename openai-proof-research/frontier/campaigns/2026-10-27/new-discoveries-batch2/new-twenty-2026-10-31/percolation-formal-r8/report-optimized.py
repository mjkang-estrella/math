from pathlib import Path
import json,re,hashlib,sys
r=Path(__file__).resolve().parent
order=(r/'optimized-extracted/module-order.txt').read_text().splitlines();g=json.loads((r/'generation.json').read_text());rows=[]
for m in order:
 if not (r/f'optimized-extracted/logs/{m}.ok').exists():break
 row={'module':m}
 for phase in ['build','check']:
  txt=(r/f'logs/{phase}-{m}.log').read_text()
  v=re.search(r'Elapsed \(wall clock\) time .*?: (\S+)',txt)[1];nums=list(map(float,v.split(':')));seconds=0
  for n in nums:seconds=seconds*60+n
  row[phase+'_seconds']=seconds;row[phase+'_rss_kib']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',txt)[1])
 row['total_seconds']=row['build_seconds']+row['check_seconds'];rows.append(row)
def totals(ms):
 a=[x for x in rows if x['module'] in ms]
 return {'modules':len(a),'compiler_seconds':round(sum(x['build_seconds'] for x in a),2),'checker_seconds':round(sum(x['check_seconds'] for x in a),2),'total_seconds':round(sum(x['total_seconds'] for x in a),2),'peak_rss_kib':max([max(x['build_rss_kib'],x['check_rss_kib']) for x in a] or [0])}
closed=5000 if any(x['module']=='MaskChain0049' for x in rows) else 0
for x in rows:
 if x['module'] in g and 'end' in g[x['module']] and x['module'].startswith('R8Chain'):closed=g[x['module']]['end']
res={'status':'partial','closed_mask_additions':closed,'remaining_additions':129671-closed,'unreplayed_suffix_zero_based':[closed,129671],'fresh_replay':totals([x['module'] for x in rows]),'windows':[],'acceptance_credit':0,'replay_tree':'Development shared-mask replay with hash-validated unchanged cached dependencies; no fresh-archive claim yet.'}
for lo,hi in [(5000,13561),(13561,14561),(13561,18561)]:
 chains=[m for m,v in g.items() if m.startswith('R8Chain') and v['start']>=lo and v['end']<=hi]
 inputs=sum([v['input_modules'] for k,v in g.items() if k.isdigit() and lo<=int(k)<hi],[])
 if not all(m in [x['module'] for x in rows] for m in chains+inputs):continue
 hints=sum(g[m]['hints'] for m in chains);t=totals(chains+inputs);c=totals(chains);t.update({'start_index':lo,'end_exclusive':hi,'hint_uses':hints,'hints_per_second':hints/t['total_seconds'],'chain_only':c,'chain_only_hints_per_second':hints/c['total_seconds'],'input_proofs':totals(inputs),'scope':'Incremental full named-dependency window, including newly needed input proofs; dependencies freshly replayed earlier in this run.'})
 last=max(order.index(m) for m in chains);ct=totals(order[:last+1]);t['cumulative_fresh_prefix']=ct;t['window_hints_over_cumulative_seconds']=hints/ct['total_seconds'];res['windows'].append(t)
res['required_heavy_1000_5000']='measured' if len(res['windows'])==3 else 'not yet fully measured'
(r/'results.json').write_text(json.dumps(res,indent=2));(r/'module-times.json').write_text(json.dumps(rows,indent=2));(r/'progress.json').write_text(json.dumps({'completed_modules':len(rows),'last_module':rows[-1]['module'] if rows else None,'closed_additions':closed,'remaining_additions':129671-closed},indent=2))
print(json.dumps(res,indent=2))
