from research import *
from collections import Counter
sources=[]
for p in sorted((H/'sources').iterdir()):
 b=p.read_bytes();sources.append({'path':str(p.relative_to(H)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
save('source-lock.json',sources)
st=json.loads((H/'screen-receipt.json').read_text());f=json.loads((H/'focused-receipt.json').read_text())
rr=json.loads((H/'registry-receipt.json').read_text())
save('provenance.json',{'status':'ZERO_NOMINEES','discovery_count_credit':0,'assigned_lane':str(H),'solo':True,'children':False,'git':False,'browser_tabs':False,'external_messages_posting_uploads':False,'guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','guard_limits':{'AS_bytes':536870912,'process_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'sampling_ms':40,'BLAS_threads':1},'source_lock':'source-lock.json','http_log':'http.jsonl','screen':{'paths':st['paths'],'unique_bodies':st['unique'],'duplicate_paths':st['duplicates'],'all_dates':True,'global_cutoff':None,'scope_limit':'Selected text hashes plus separate broader uncapped native regex; not semantic clearance','focused_receipt':f},'registry':rr,'failures':'progress.md','mathematical_status':{'domino':'unresolved; full positive quotient missing','partite':'unresolved; all-host lower bound missing; journal body403','spectral':'public full theorem; excluded'},'counts_observed':{'additional':9,'total':39,'next':40},'mutable_coordination_separate':['NEXT-as-read.md','context-receipts.json']})
# Context disposition review: inspect all current records, emit compact audit receipt.
ctx=[]
for n in ['ledger.json','prior-campaign-context.json']:
 x=json.loads((H.parent.parent/n).read_text())
 for k,v in x.items():
  if isinstance(v,list):
   for a in v:
    if isinstance(a,dict):ctx.append({'file':n,'section':k,'title':a.get('title',a.get('target',a.get('path'))),'status':a.get('status'),'scope':a.get('scope')})
save('context-dispositions.json',ctx)
print('context records',len(ctx));print('screen',st['paths'],st['unique'],st['duplicates']);print('focused',f)
