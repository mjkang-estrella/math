from research import *
B=HERE.parent.parent
paths=[ROOT/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',ROOT/'sources/upstream.json',ROOT/'sources/CONTENTS.md',ROOT/'sources/preprints-tree.json']
paths += [B/f'lanes/root-r{n}-handback/DECISION.md' for n in [119,120,121]]
paths += [B/'lanes/sol-fresh-source-discovery-r122'/n for n in ['SUMMARY.md','discovery.md','registry-coverage.json']]
(HERE/'context').mkdir(exist_ok=True);r=[]
for i,p in enumerate(paths):
 b=p.read_bytes();dest=HERE/'context'/f'{i:02d}-{p.name}';dest.write_bytes(b);r.append({'path':str(p),'copy':str(dest.relative_to(HERE)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'role':'mutable coordination' if p.name=='NEXT.md' else 'inherited context'})
 if p.name in ['ledger.json','prior-campaign-context.json']:
  j=json.loads(b);print(p.name,{'accepted_count':j.get('accepted_count'),'total_accepted_count':j.get('total_accepted_count'),'accepted_titles':[x.get('title',x.get('source_target')) for x in j.get('accepted',[])]})
save('context-receipts.json',{'utc':utc(),'files':r})
text=(HERE/'source-imv.txt').read_text()
for a,b in [('Subdivision of complete graphs','Complexity issues'),('Concluding remarks','Data Availability')]:
 i=text.find(a);j=text.find(b,i+len(a));print(text[i:j])
