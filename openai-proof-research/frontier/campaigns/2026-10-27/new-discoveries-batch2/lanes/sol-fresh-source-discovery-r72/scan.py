import pathlib,json,re,hashlib,datetime
root=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
terms=['Zinn','208349','451831','Jekl','1409.6411','328867','1452-86302600011']
summary=[]
for p in root.glob('frontier/**/SUMMARY.md'):
 if '/extracted' in str(p) or '/frozen/' in str(p):continue
 s=p.read_text(errors='replace')
 hits=[t for t in terms if re.search(re.escape(t),s,re.I)]
 if hits:summary.append({'file':str(p),'terms':hits,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
trees=[]
base=root/'frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes'
for lane in ['sol-fresh-source-discovery-r57','sol-fresh-source-discovery-r58']:
 for p in (base/lane/'sources').glob('*.json'):
  try:d=json.loads(p.read_text())
  except:continue
  if not isinstance(d,dict) or 'tree' not in d:continue
  hits=[x['path'] for x in d['tree'] if re.search('Zinn|Rademacher|Pinelis|Haagerup|Jekl',x['path'],re.I)]
  trees.append({'file':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'sha':d.get('sha'),'truncated':d.get('truncated'),'hits':hits})
context=[]
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json','NEXT.md']:
 p=base.parent/name;s=p.read_text();context.append({'file':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':len(p.read_bytes()),'headings':re.findall(r'^#+ .*',s,re.M)})
json.dump({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'summary_hits':summary,'trees':trees,'context':context},open('scan.json','w'),indent=2)
print(json.dumps({'summary_hits':summary,'tree_hits':[{ 'file':x['file'],'hits':x['hits']} for x in trees]},indent=2))
